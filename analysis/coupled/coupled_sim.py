"""Coupled recursive-viability simulation (radCAD).

One shared state x is driven by:
- drift θ_t: piecewise constant;
- memory m_t;
- shocks d_t, attenuated by Skin (σ) and Spotlight (α);
- a feedback loop with gain k (Brake) and an optional one-step delay.

The shared resource stock R pays capacity costs plus a deviation cost κ|x|. A run dies when
|x| > X or R < 0.

Families
  F  formal-matched: uniform |d| ≤ D, at most one shift, oracle Watcher with latency lat,
     brake gain 1/4, κ = 0. This is exactly the Lean model (FiveOrgans/Coupled.lean).
  S  stochastic: Poisson shifts, estimating Watcher with threshold τ (false resets possible),
     deviation-coupled resources.
  H  as S, but shocks are Student-t(3) and unbounded. This violates the formal assumption |d| ≤ D.

All 32 configurations share each seed's drift and shock path (common random numbers).
Usage: python coupled_sim.py dev|confirm
"""
import sys, json, math, hashlib, itertools, time
import numpy as np

CFGS = list(itertools.product([0, 1], repeat=5))          # (S, M, P, B, W)
NAMES = ["".join("SMPBW"[i] for i in range(5) if c[i]) or "-" for c in CFGS]
CA = np.array(CFGS, dtype=bool)                            # 32 x 5
T = 2000
BLOCK = 200
COST = 0.1


# ---------- formal mirror of the Lean decision rule (FiveOrgans.Coupled.viable_closed) ----------
def Hc(l, B, delay):
    if B:
        return 4 - 2 * (l + 2) / 2 ** l if delay else 4 - 4 * 0.75 ** l
    return 1.0


def formal(c, e):
    S, M, P, B, W = c
    sf = (e["sigma"] if S else 1) * (e["alpha"] if P else 1)
    lat = 1 if P else e["K"]
    L1 = 4 if B else 1
    if M:
        dr = (2 * e["Theta"] * (Hc(lat, B, e["delay"]) if W else L1)) if e["shift"] else 0.0
    else:
        dr = e["Theta"] * L1
    peak = sf * e["D"] * L1 + dr
    cost = COST * sum(c)
    stable = B or not e["delay"]
    return dict(peak=peak, viable=bool(cost <= e["income"] and stable and peak <= e["X"]),
                stable=bool(stable), L1=L1)


def selftest():
    """Mirror must reproduce the seven Lean ablation tables (CoupledAblation.lean)."""
    def mk(D, Th, X, K, dl, sh, inc):
        return dict(D=D, Theta=Th, X=X, sigma=.5, alpha=.5, K=K, delay=dl, shift=sh, income=inc)
    want = {"calm": (mk(1, 0, 1.5, 3, 0, 0, 1), 20), "delayE": (mk(1, 0, 4, 3, 1, 0, 1), 16),
            "shiftFast": (mk(1, 1, 4, 1, 1, 1, 1), 3), "shiftSlow": (mk(1, 1, 4, 4, 1, 1, 1), 2),
            "deadbeatShift": (mk(1, 1, 1.5, 3, 0, 1, 1), 6), "hostile": (mk(1, .25, 1.75, 3, 1, 1, 1), 1),
            "poor": (mk(1, .25, 1.75, 3, 1, 1, .4), 0)}
    for k, (e, n) in want.items():
        got = sum(formal(c, e)["viable"] for c in CFGS)
        assert got == n, (k, got, n)


# ---------- environment families ----------
def draw_envs(family, n, seed, heldout):
    r = np.random.default_rng(seed)
    out = []
    for i in range(n):
        e = dict(family=family, idx=i, D=1.0,
                 Theta=float(r.uniform(0.5, 2.0) if heldout else r.uniform(0.0, 1.5)),
                 X=float(r.uniform(2.0, 10.0) if heldout else r.uniform(1.0, 8.0)),
                 sigma=float(r.uniform(0.3, 0.9)), alpha=float(r.uniform(0.3, 0.9)),
                 K=int(r.integers(1, 9)), delay=bool(r.random() < 0.5), shift=bool(r.random() < 0.6),
                 kB=0.25, tau_c=1.0, R0=10.0)
        if family == "F":
            e.update(income=float(r.choice([0.25, 1.0], p=[0.15, 0.85])), kappa=0.0, rate=0.0)
        else:
            e.update(income=float(r.uniform(0.3, 1.0)), kappa=float(r.uniform(0.0, 0.002)),
                     rate=float(r.uniform(0.001, 0.01)), tau_c=float(r.uniform(0.5, 1.5)))
        out.append(e)
    return out


# ---------- vectorised dynamics over (32 configs x S seeds [x N units]) ----------
class Sim:
    def __init__(self, e, seeds, units=1, eta=0.0, ablate=None):
        self.e = e
        nS = len(seeds)
        self.nS, self.units = nS, units
        shape = (32, nS, units)
        self.shape = shape
        c = CA[:, None, None, :]                                   # 32 x 1 x 1 x 5
        S_, M_, P_, B_, W_ = (np.broadcast_to(c[..., i], shape).copy() for i in range(5))
        if ablate is not None:                                     # partial ablation of units
            organ, frac = ablate
            j = "SMPBW".index(organ)
            k = int(round(frac * units))
            if k:
                [S_, M_, P_, B_, W_][j][:, :, :k] = False
        self.S, self.M, self.P, self.B, self.W = S_, M_, P_, B_, W_
        self.sf = np.where(S_, e["sigma"], 1.0) * np.where(P_, e["alpha"], 1.0)
        self.L = np.where(P_, 1, e["K"])
        self.k = np.where(B_, e["kB"], 1.0)
        self.cost = COST * (S_.astype(int) + M_ + P_ + B_ + W_)
        # per-seed exogenous paths (common random numbers across configurations)
        th = np.empty((nS, T)); d = np.empty((nS, T)); eps = np.zeros((nS, units, T))
        shifts = []
        for si, sd in enumerate(seeds):
            r = np.random.default_rng([sd, e["idx"], ord(e["family"])])
            th0 = r.uniform(-e["Theta"], e["Theta"])
            path = np.full(T, th0); st = []
            if e["shift"]:
                if e["family"] == "F":
                    s0 = int(r.integers(0, T // 2)); path[s0:] = r.uniform(-e["Theta"], e["Theta"]); st = [s0]
                else:
                    t = 0
                    while True:
                        t += int(r.geometric(e["rate"]))
                        if t >= T: break
                        path[t:] = r.uniform(-e["Theta"], e["Theta"]); st.append(t)
            th[si] = path; shifts.append(st)
            if e["family"] == "H":
                d[si] = e["D"] / 2 * r.standard_t(3, T)
            else:
                d[si] = r.uniform(-e["D"], e["D"], T)
            if units > 1:
                eps[si] = r.uniform(-eta, eta, (units, T))
        self.th, self.d, self.eps, self.shifts = th, d, eps, shifts
        self.is_shift = np.zeros((nS, T), bool)
        for si, st in enumerate(shifts):
            self.is_shift[si, st] = True
        self.th0 = th[:, 0]
        z = lambda: np.zeros(shape)
        self.x, self.xp = z(), z()
        self.m = np.where(M_, self.th0[None, :, None], 0.0)
        self.R = np.full(shape, e["R0"])
        self.alive = np.ones(shape, bool)
        self.ttd = np.full(shape, T)
        self.acc = z(); self.cnt = np.zeros(shape, int)          # watcher window
        self.tau = e["tau_c"] * self.sf * e["D"]
        # metrics
        self.coh, self.absx, self.err, self.absth, self.peak = z(), z(), z(), z(), z()
        self.rec_sum, self.rec_n, self.since = z(), z(), np.full(shape, -1.0)
        self.det_true, self.det_false, self.nshift = z(), z(), z()
        self.last_shift = np.full((nS,), -10 ** 6); self.detected = np.ones(shape, bool)
        # aggregate (micro) tracking
        self.agg_alive = np.ones((32, nS), bool); self.agg_ttd = np.full((32, nS), T)
        self.t = 0

    def step(self):
        e, t = self.e, self.t
        th = self.th[:, t][None, :, None]
        if e["family"] == "F":                                   # oracle Watcher, exact Lean model
            tl = np.clip(t - self.L, 0, None)
            th_lag = np.take_along_axis(np.broadcast_to(self.th[None, :, None, :], self.shape + (T,)),
                                        tl[..., None], axis=-1)[..., 0]
            mW = np.where(t >= self.L, th_lag, self.th0[None, :, None])
            self.m = np.where(self.M, np.where(self.W, mW, self.th0[None, :, None]), 0.0)
        w = th - self.m + self.sf * self.d[:, t][None, :, None] + self.eps[:, :, t][None]
        a = self.alive
        # metrics before update
        self.err += np.where(a, np.abs(th - self.m), 0); self.absth += np.where(a, np.abs(th), 0)
        if self.is_shift[:, t].any():
            sh = self.is_shift[:, t][None, :, None] & a
            self.since = np.where(sh, 0.0, self.since)
            self.nshift += sh
            self.last_shift = np.where(self.is_shift[:, t], t, self.last_shift)
            self.detected = np.where(sh, False, self.detected)
        # estimating Watcher (families S, H)
        if e["family"] != "F":
            act = self.M & self.W & a
            self.acc += np.where(act, w, 0); self.cnt += act
            full = act & (self.cnt >= self.L)
            mean = np.where(full, self.acc / np.maximum(self.cnt, 1), 0)
            fire = full & (np.abs(mean) > self.tau)
            self.m = np.where(fire, self.m + mean, self.m)
            recent = (t - self.last_shift[None, :, None]) <= 2 * self.L + 5
            tp = fire & recent & ~self.detected
            self.det_true += tp; self.det_false += fire & ~tp
            self.detected |= tp
            self.acc = np.where(full, 0, self.acc); self.cnt = np.where(full, 0, self.cnt)
        # shared loop
        if e["delay"]:
            xn = self.x - self.k * self.xp + w
        else:
            xn = (1 - self.k) * self.x + w
        self.xp = np.where(a, self.x, self.xp); self.x = np.where(a, xn, self.x)
        self.R = np.where(a, self.R + e["income"] - self.cost - e["kappa"] * np.abs(self.x), self.R)
        ax = np.abs(self.x)
        self.coh += np.where(a, ax <= e["X"] / 2, 0); self.absx += np.where(a, ax, e["X"])
        self.peak = np.where(a, np.maximum(self.peak, ax), self.peak)
        rec = a & (self.since >= 0) & ((ax < e["X"] / 4) | (self.since >= 200))
        self.rec_sum += np.where(rec, self.since, 0); self.rec_n += rec
        self.since = np.where(rec, -1, np.where(self.since >= 0, self.since + 1, -1))
        if self.units == 1:
            dead = a & ((ax > e["X"]) | (self.R < 0))
        else:   # micro mode: units never die individually; only the aggregate (macro) variable can
            ag = (np.abs(self.x.mean(axis=2)) > e["X"]) | (self.R.mean(axis=2) < 0)
            nd = self.agg_alive & ag
            self.agg_ttd = np.where(nd, t + 1, self.agg_ttd); self.agg_alive &= ~ag
            dead = np.broadcast_to(nd[:, :, None], self.shape)
        self.ttd = np.where(dead, t + 1, self.ttd); self.alive = a & ~dead
        self.t += 1

    def metrics(self):
        e = self.e
        life = np.maximum(self.ttd, 1)
        absx = self.absx / T
        out = dict(
            survival=self.alive.mean(axis=(1, 2)) if self.units == 1 else self.agg_alive.mean(axis=1),
            unit_survival=self.alive.mean(axis=(1, 2)),
            ttd=self.ttd.mean(axis=(1, 2)),
            coherence=(self.coh / life).mean(axis=(1, 2)),
            recovery=np.nanmean(np.where(self.rec_n > 0, self.rec_sum / np.maximum(self.rec_n, 1), np.nan),
                                axis=(1, 2)) if (self.rec_n > 0).any() else np.full(32, np.nan),
            retention=(1 - self.err.sum(axis=(1, 2)) / np.maximum(self.absth.sum(axis=(1, 2)), 1e-12)),
            regret=(absx - absx.min(axis=0, keepdims=True)).mean(axis=(1, 2)),
            detection=self.det_true.sum(axis=(1, 2)) / np.maximum(self.nshift.sum(axis=(1, 2)), 1),
            false_alarm=self.det_false.sum(axis=(1, 2)) / (life.sum(axis=(1, 2))),
            amplification=(self.peak / (self.sf * e["D"])).mean(axis=(1, 2)),
            surv_seed=(self.alive.all(axis=2) if self.units == 1 else self.agg_alive).astype(int),
        )
        return out


def run_env_radcad(e, seeds, **kw):
    """Advance one environment with radCAD: each radCAD timestep runs BLOCK steps of the model."""
    from radcad import Model, Simulation, Experiment
    from radcad.engine import Engine, Backend
    holder = {}

    def p_block(params, substep, sh, prev):
        sim = holder.setdefault("sim", Sim(e, seeds, **kw))
        for _ in range(min(BLOCK, T - sim.t)):
            sim.step()
        return {"t": sim.t}

    blocks = [{"policies": {"b": p_block}, "variables": {"t": lambda p, ss, sh, prev, pi: ("t", pi["t"])}}]
    model = Model(initial_state={"t": 0}, state_update_blocks=blocks, params={})
    sim = Simulation(model=model, timesteps=math.ceil(T / BLOCK), runs=1)
    exp = Experiment([sim])
    exp.engine = Engine(backend=Backend.SINGLE_PROCESS, deepcopy=False, drop_substeps=True)
    res = exp.run()
    assert res[-1]["t"] == T
    return holder["sim"].metrics()


def table(envs, seeds, **kw):
    rows = []
    for e in envs:
        mt = run_env_radcad(e, seeds, **kw)
        for ci, c in enumerate(CFGS):
            f = formal(c, e)
            row = dict(family=e["family"], env=e["idx"], cfg=NAMES[ci], S=c[0], M=c[1], P=c[2], B=c[3], W=c[4],
                       delay=e["delay"], shift=e["shift"], K=e["K"], X=e["X"], peak=f["peak"],
                       viable=f["viable"], stable=f["stable"], L1=f["L1"],
                       surv_seed=mt["surv_seed"][ci].tolist())
            for k, v in mt.items():
                if k != "surv_seed":
                    row[k] = float(v[ci])
            rows.append(row)
    return rows


# ---------- pre-registered analyses ----------
def boot_ci(vals_by_env, B=2000, seed=7):
    v = np.asarray(vals_by_env, float)
    v = v[~np.isnan(v)]
    if len(v) == 0:
        return (np.nan, np.nan, np.nan)
    r = np.random.default_rng(seed)
    bs = r.choice(v, (B, len(v))).mean(axis=1)
    return (float(v.mean()), float(np.quantile(bs, .025)), float(np.quantile(bs, .975)))


def analyse(rows, rows_mis, rows_lat, rows_micro, rows_part):
    import pandas as pd
    df = pd.DataFrame(rows)
    R = {}
    F = df[df.family == "F"]
    # H1 soundness: no death among formally viable configurations in F (seed level)
    fv = F[F.viable]
    deaths = int(sum(len(s) - sum(s) for s in fv.surv_seed))
    R["H1"] = dict(viable_runs=int(sum(len(s) for s in fv.surv_seed)), deaths=deaths, falsified=deaths > 0)
    # H2 viable survive more often than non-viable in F
    sv, sn = F[F.viable].survival.mean(), F[~F.viable].survival.mean()
    R["H2"] = dict(surv_viable=float(sv), surv_nonviable=float(sn), falsified=bool(sn >= sv))
    S = df[df.family == "S"]
    # H3 brake necessary under delay (S)
    s3 = S[S.delay & (S.B == 0)].survival.mean()
    R["H3"] = dict(surv_noB_delay=float(s3), falsified=bool(s3 > 0.05))

    def contrast(sub, f):
        vals = []
        for env, g in sub.groupby("env"):
            vals.append(f(g))
        return boot_ci(vals)
    sh = S[S["shift"] & (S.B == 1)]
    # H4 M-W complementarity: interaction contrast on survival
    def inter(col):
        def f(g):
            q = lambda m, w: g[(g.M == m) & (g.W == w)][col].mean()
            return q(1, 1) - q(1, 0) - q(0, 1) + q(0, 0)
        return f
    m4 = contrast(sh, inter("regret")); m4s = contrast(sh, inter("survival"))
    # complementarity = M and W together reduce regret more than the sum of their separate effects
    R["H4"] = dict(mean=m4[0], lo=m4[1], hi=m4[2], survival_secondary=m4s, falsified=bool(not m4[2] < 0))
    # H5 memory without watcher harmful under shifts: higher regret than no memory
    d5 = lambda col: (lambda g: g[(g.M == 1) & (g.W == 0)][col].mean() - g[(g.M == 0) & (g.W == 0)][col].mean())
    m5 = contrast(sh, d5("regret")); m5s = contrast(sh, d5("survival"))
    R["H5"] = dict(mean=m5[0], lo=m5[1], hi=m5[2], survival_secondary=m5s, falsified=bool(not m5[1] > 0))
    # H6 misconfiguration: low watcher threshold raises regret of M∧W configs (no-shift S envs)
    dm = pd.DataFrame(rows_mis)
    def h6(g):
        a = g[(g.M == 1) & (g.W == 1) & (g.tag == "low")].regret.mean()
        b = g[(g.M == 1) & (g.W == 1) & (g.tag == "nominal")].regret.mean()
        return a - b
    m6 = contrast(dm, h6)
    fa = dm[(dm.M == 1) & (dm.W == 1)].groupby("tag").false_alarm.mean().to_dict()
    R["H6"] = dict(mean=m6[0], lo=m6[1], hi=m6[2], false_alarm=fa, falsified=bool(not m6[1] > 0))
    # H7 latency hurts M∧W∧B without Spotlight more than with it
    dl = pd.DataFrame(rows_lat)
    def h7(g):
        q = lambda p, K: g[(g.M == 1) & (g.W == 1) & (g.B == 1) & (g.P == p) & (g.K == K)].survival.mean()
        return (q(0, 1) - q(0, 8)) - (q(1, 1) - q(1, 8))
    m7 = contrast(dl, h7)
    R["H7"] = dict(mean=m7[0], lo=m7[1], hi=m7[2], falsified=bool(not m7[1] > 0))
    # H8 uniform interventions transfer: formally viable with margin => aggregate never fails
    du = pd.DataFrame(rows_micro)
    ok = du[du.viable & (du.X - du.peak > du.eta * du.L1)]
    d8 = int(sum(len(s) - sum(s) for s in ok.surv_seed))
    R["H8"] = dict(cells=len(ok), runs=int(sum(len(s) for s in ok.surv_seed)), agg_deaths=d8, falsified=d8 > 0)
    # H9 partial ablation of the Brake under delay breaks majority-config transfer
    dp = pd.DataFrame(rows_part)
    base = dp[dp.viable & (dp.B == 1)]
    m9 = contrast(base, lambda g: g[g.frac == 0.25].survival.mean() - g[g.frac == 0.0].survival.mean())
    means = base.groupby("frac").survival.mean()
    mono = bool(all(np.diff(means.sort_index().values) <= 1e-12))
    R["H9"] = dict(cells=int((base.frac == 0).sum()), mean=m9[0], lo=m9[1], hi=m9[2], monotone=mono,
                   falsified=bool(not (m9[2] < 0 and mono)))
    R["H9_by_frac"] = dp[dp.viable & (dp.B == 1)].groupby("frac").survival.mean().to_dict()
    # H10 out-of-validity (heavy tails) + cross-environment rank generalisation
    Hh = df[df.family == "H"]
    R["H10a"] = dict(death_rate_viable=float(1 - Hh[Hh.viable].survival.mean()) if Hh.viable.any() else None,
                     falsified=bool(Hh.viable.any() and Hh[Hh.viable].survival.mean() >= 1.0))
    from scipy.stats import spearmanr
    rho = {}
    for fam in ["S", "H"]:
        rs = []
        for env, g in df[df.family == fam].groupby("env"):
            margin = np.where(g.stable, (g.X - g.peak) / g.X, -10.0)
            if np.std(g.survival) > 0:
                rs.append(spearmanr(margin, g.survival).statistic)
        rho[fam] = dict(median=float(np.median(rs)), frac_gt_half=float(np.mean(np.array(rs) > 0.5)), n=len(rs))
    R["H10b"] = dict(rho=rho, falsified=bool(any(v["frac_gt_half"] <= 0.5 for v in rho.values())))
    # descriptive: per-capacity necessity / sufficiency / redundancy / harm per environment (S)
    desc = {}
    for env, g in S.groupby("env"):
        best = g.survival.max()
        good = g[g.survival >= best - 0.02]
        desc[int(env)] = dict(best=float(best), necessary=[o for o in "SMPBW" if (good[o] == 1).all()],
                              never_needed=[o for o in "SMPBW" if (good[o] == 0).any()])
    R["desc_S"] = desc
    R["metrics_by_cfg_S"] = S.groupby("cfg")[["survival", "coherence", "recovery", "retention", "regret",
                                             "detection", "false_alarm", "amplification"]].mean().round(4).to_dict("index")
    return R


def main(mode):
    selftest()
    if mode == "dev":
        seeds = list(range(0, 12)); nE = 6; es = 101; held = False
    else:
        seeds = list(range(10000, 10040)); nE = 20; es = 202; held = True
    t0 = time.time()
    envs = draw_envs("F", nE, es, held) + draw_envs("S", nE, es + 1, held) + draw_envs("H", nE, es + 2, held)
    rows = table(envs, seeds)
    # H6: misconfiguration (no-shift stochastic environments, nominal vs low threshold)
    mis = []
    for e in draw_envs("S", nE, es + 3, held):
        e = dict(e, shift=False)
        for tag, tc in [("nominal", 1.0), ("low", 0.2)]:
            for r in table([dict(e, tau_c=tc)], seeds):
                mis.append(dict(r, tag=tag))
    # H7: latency (shift + delay environments, K = 1 vs 8)
    lat = []
    for e in draw_envs("S", nE, es + 4, held):
        for K in (1, 8):
            lat += table([dict(e, K=K, shift=True, delay=True)], seeds)
    # H8: uniform interventions, micro N = 20 units, eta = 0.1 D (family F)
    micro = []
    for e in draw_envs("F", nE, es + 5, held):
        for r in table([e], seeds[: len(seeds) // 2], units=20, eta=0.1):
            micro.append(dict(r, eta=0.1))
    # H9: partial ablation of the Brake under delay (family F, delay forced)
    part = []
    for e in draw_envs("F", nE, es + 6, held):
        e = dict(e, delay=True)
        for frac in (0.0, 0.05, 0.1, 0.25):
            for r in table([e], seeds[: len(seeds) // 2], units=20, eta=0.1, ablate=("B", frac)):
                part.append(dict(r, frac=frac))
    import os, gzip
    here = os.path.dirname(os.path.abspath(__file__))
    with gzip.open(os.path.join(here, f"coupled_{mode}_rows.json.gz"), "wt") as fh:
        json.dump(dict(main=rows, mis=mis, lat=lat, micro=micro, part=part), fh,
                  default=lambda o: o.item() if hasattr(o, "item") else str(o))
    R = analyse(rows, mis, lat, micro, part)
    R["_meta"] = dict(mode=mode, seeds=[seeds[0], seeds[-1]], n_env_per_family=nE, env_seed=es,
                      heldout_ranges=held, T=T, runtime_s=round(time.time() - t0, 1),
                      script_sha256=hashlib.sha256(open(__file__, "rb").read()).hexdigest())
    out = f"coupled_{mode}_results.json"
    import os
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), out)
    with open(path, "w") as fh:
        json.dump(R, fh, indent=1, default=lambda o: o.item() if hasattr(o, "item") else str(o))
    for k in sorted(R):
        if k.startswith("H"):
            print(k, json.dumps(R[k], default=str)[:400])
    print("meta", R["_meta"])


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "dev")
