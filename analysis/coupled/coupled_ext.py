"""Extension of the coupled simulation (pre-registered separately: PREREG_coupled_ext_2026-11-23.md).

Imports the frozen coupled_sim.py unchanged and adds:
- adaptation time after each drift shift: steps until |θ − m| ≤ ¼|Δθ|, capped at 300;
- resistance to destabilising feedback: a parasitic term δ·x_t is added to x_{t+1}.
  Resistance is the largest δ on a grid with survival ≥ 0.9 at that δ and every smaller one
  (−0.1 if δ = 0 already fails);
- mid-run organ failure at t = T/2, giving compensation and propagation contrasts;
- heterogeneous micro units, each with its own config drawn from the viable-with-margin set.

Usage: python coupled_ext.py dev|confirm
"""
import sys, os, json, math, time, hashlib
import numpy as np
import coupled_sim as cs
from coupled_sim import CFGS, NAMES, CA, T, BLOCK, COST, formal, draw_envs, boot_ci

CAP = 300
DGRID = [0.0, 0.1, 0.2, 0.3, 0.5, 0.8]


class ExtSim(cs.Sim):
    def __init__(self, e, seeds, delta=0.0, fail=None, unit_cfgs=None, **kw):
        super().__init__(e, seeds, **kw)
        self.delta, self.fail = delta, fail
        if unit_cfgs is not None:                       # array (32, units, 5) of bools
            U = np.broadcast_to(unit_cfgs[:, None, :, :], self.shape + (5,))
            self.S, self.M, self.P, self.B, self.W = (U[..., i].copy() for i in range(5))
            self._recompute(retau=True)
            self.m = np.where(self.M, self.th0[None, :, None], 0.0)
        z = lambda: np.zeros(self.shape)
        self.clock = np.full(self.shape, -1.0); self.target = z()
        self.ad_sum, self.ad_n, self.ad_bad = z(), z(), z()

    def _recompute(self, retau):
        e = self.e
        self.sf = np.where(self.S, e["sigma"], 1.0) * np.where(self.P, e["alpha"], 1.0)
        self.L = np.where(self.P, 1, e["K"])
        self.k = np.where(self.B, e["kB"], 1.0)
        self.cost = COST * (self.S.astype(int) + self.M + self.P + self.B + self.W)
        if retau:
            self.tau = e["tau_c"] * self.sf * e["D"]

    def _fail(self, organ):
        a = {"S": "S", "M": "M", "P": "P", "B": "B", "W": "W"}[organ]
        setattr(self, a, np.zeros(self.shape, bool))
        self._recompute(retau=False)        # Watcher threshold keeps its design-time calibration
        if organ == "M":
            self.m = np.zeros(self.shape)

    def step(self):
        t = self.t
        if self.fail is not None and t == self.fail[1]:
            self._fail(self.fail[0])
        xold = self.x.copy()
        LL = self.L.copy()
        super().step()
        e = self.e
        if self.delta:
            a = self.alive
            self.x = np.where(a, self.x + self.delta * xold, self.x)
            dead = a & (np.abs(self.x) > e["X"])
            self.ttd = np.where(dead, t + 1, self.ttd); self.alive = a & ~dead
        a = self.alive
        th = self.th[:, t][None, :, None]
        err = np.abs(th - self.m)
        if t > 0 and self.is_shift[:, t].any():
            dth = np.abs(self.th[:, t] - self.th[:, t - 1])[None, :, None]
            start = self.is_shift[:, t][None, :, None] & (dth > 0) & a
            self.clock = np.where(start, 0.0, self.clock)
            self.target = np.where(start, 0.25 * dth, self.target)
        run = (self.clock >= 0) & a
        hit = run & (err <= self.target)
        cap = run & ~hit & (self.clock >= CAP)
        rec = hit | cap
        val = np.where(hit, self.clock, CAP)
        self.ad_sum += np.where(rec, val, 0); self.ad_n += rec
        mw = self.M & self.W
        self.ad_bad += rec & mw & (val != LL)
        self.clock = np.where(rec, -1.0, np.where(run, self.clock + 1, np.where(a, self.clock, -1.0)))

    def metrics(self):
        out = super().metrics()
        out["adapt"] = np.where(self.ad_n.sum(axis=(1, 2)) > 0,
                                self.ad_sum.sum(axis=(1, 2)) / np.maximum(self.ad_n.sum(axis=(1, 2)), 1), np.nan)
        out["adapt_bad"] = self.ad_bad.sum(axis=(1, 2))
        out["adapt_n"] = self.ad_n.sum(axis=(1, 2))
        return out


def run(e, seeds, **kw):
    from radcad import Model, Simulation, Experiment
    from radcad.engine import Engine, Backend
    holder = {}

    def p_block(params, substep, sh, prev):
        sim = holder.setdefault("sim", ExtSim(e, seeds, **kw))
        for _ in range(min(BLOCK, T - sim.t)):
            sim.step()
        return {"t": sim.t}
    blocks = [{"policies": {"b": p_block}, "variables": {"t": lambda p, ss, sh, prev, pi: ("t", pi["t"])}}]
    exp = Experiment([Simulation(model=Model(initial_state={"t": 0}, state_update_blocks=blocks, params={}),
                                 timesteps=math.ceil(T / BLOCK), runs=1)])
    exp.engine = Engine(backend=Backend.SINGLE_PROCESS, deepcopy=False, drop_substeps=True)
    assert exp.run()[-1]["t"] == T
    return holder["sim"].metrics()


def rows_of(e, mt, **extra):
    out = []
    for ci, c in enumerate(CFGS):
        f = formal(c, e)
        r = dict(env=e["idx"], family=e["family"], cfg=NAMES[ci], S=c[0], M=c[1], P=c[2], B=c[3], W=c[4],
                 delay=e["delay"], shift=e["shift"], K=e["K"], X=e["X"], viable=f["viable"], peak=f["peak"], L1=f["L1"])
        for k, v in mt.items():
            if k != "surv_seed":
                r[k] = float(v[ci])
        r.update(extra); out.append(r)
    return out


def ci(vals):
    return boot_ci(vals)


def main(mode):
    cs.selftest()
    if mode == "dev":
        seeds = list(range(0, 12)); nE = 6; es = 501; held = False
    else:
        seeds = list(range(20000, 20040)); nE = 20; es = 602; held = True
    t0 = time.time(); R = {}
    import pandas as pd
    # ---- E1 resistance (no shift, uniform shocks, ample income; half delay, half no delay)
    res = []
    for j, e in enumerate(draw_envs("F", nE, es, held)):
        e = dict(e, shift=False, income=1.0, delay=(j % 2 == 0))
        surv = {d: run(e, seeds, delta=d)["survival"] for d in DGRID}
        for ci_, c in enumerate(CFGS):
            r = -0.1
            for d in DGRID:
                if surv[d][ci_] >= 0.9: r = d
                else: break
            res.append(dict(env=j, delay=e["delay"], B=c[3], cfg=NAMES[ci_], resist=r, surv0=float(surv[0.0][ci_])))
    dr = pd.DataFrame(res)
    for dl, key in [(False, "E1a"), (True, "E1b")]:
        sub = dr[dr.delay == dl]
        diff = [g[g.B == 1].resist.mean() - g[g.B == 0].resist.mean() for _, g in sub.groupby("env")]
        m = ci(diff)
        ok = (m[2] < 0) if not dl else (m[1] > 0)
        R[key] = dict(B_minus_noB=m, falsified=bool(not ok),
                      mean_resist={f"B={k}": v for k, v in sub.groupby("B").resist.mean().items()})
    sub = dr[(dr.surv0 >= 0.9)]
    R["E1_secondary_survivors_only"] = {f"delay={k[0]},B={k[1]}": v for k, v in sub.groupby(["delay", "B"]).resist.mean().items()}
    # ---- E2 adaptation
    ad = []
    for e in draw_envs("F", nE, es + 1, held):
        e = dict(e, shift=True)
        ad += rows_of(e, run(e, seeds), fam="F")
    for e in draw_envs("S", nE, es + 2, held):
        e = dict(e, shift=True, rate=max(e["rate"], 0.003))
        ad += rows_of(e, run(e, seeds), fam="S")
    da = pd.DataFrame(ad)
    fmw = da[(da.fam == "F") & (da.M == 1) & (da.W == 1)]
    R["E2a"] = dict(records=float(fmw.adapt_n.sum()), violations=float(fmw.adapt_bad.sum()),
                    falsified=bool(fmw.adapt_bad.sum() > 0 or fmw.adapt_n.sum() == 0))
    S2 = da[(da.fam == "S") & (da.M == 1)]
    m = ci([g[g.W == 1].adapt.mean() - g[g.W == 0].adapt.mean() for _, g in S2.groupby("env")])
    R["E2b"] = dict(W_minus_noW=m, falsified=bool(not m[2] < 0))
    S3 = S2[S2.W == 1]
    m = ci([g[g.P == 1].adapt.mean() - g[g.P == 0].adapt.mean() for _, g in S3.groupby("env")])
    R["E2c"] = dict(P_minus_noP=m, falsified=bool(not m[2] < 0))
    R["E2_by_cfg_S"] = da[da.fam == "S"].groupby("cfg").adapt.mean().round(2).to_dict()
    # ---- E3 compensation and propagation (mid-run failure at T/2)
    comp = []
    for e in draw_envs("S", nE, es + 3, held):
        e = dict(e, shift=True, rate=max(e["rate"], 0.003))
        base = rows_of(e, run(e, seeds), organ="none")
        comp += base
        for o in "SMPBW":
            comp += rows_of(e, run(e, seeds, fail=(o, T // 2)), organ=o)
    dc = pd.DataFrame(comp)
    key = ["env", "cfg"]
    b = dc[dc.organ == "none"].set_index(key)
    deltas = []
    for o in "SMPBW":
        f = dc[dc.organ == o].set_index(key)
        d = (f[["survival", "false_alarm", "adapt", "retention"]] - b[["survival", "false_alarm", "adapt", "retention"]])
        d = d.join(b[["S", "M", "P", "B", "W", "delay"]]).reset_index(); d["organ"] = o
        deltas.append(d[d[o] == 1])
    dd = pd.concat(deltas)
    C = {}
    for o in "SMPBW":
        for o2 in "SMPBW":
            if o2 == o: continue
            g = dd[dd.organ == o]
            C[f"{o}<-{o2}"] = ci([h[h[o2] == 1].survival.mean() - h[h[o2] == 0].survival.mean() for _, h in g.groupby("env")])
    R["compensation_matrix"] = C
    R["E3a"] = dict(C_S_by_P=C["S<-P"], falsified=bool(not C["S<-P"][1] > 0))
    gB = dd[(dd.organ == "B") & dd.delay]
    m = ci([h.survival.mean() for _, h in gB.groupby("env")]) if len(gB) else [None] * 3
    R["E3b"] = dict(delta_surv=m, falsified=bool(len(gB) == 0 or not m[2] < 0))
    g = dd[(dd.organ == "S") & (dd.M == 1) & (dd.W == 1)]
    m = ci([h.false_alarm.mean() for _, h in g.groupby("env")])
    R["E3c"] = dict(delta_false_alarm=m, falsified=bool(not m[1] > 0))
    g = dd[(dd.organ == "P") & (dd.M == 1) & (dd.W == 1)]
    m = ci([h.adapt.mean() for _, h in g.groupby("env")])
    R["E3d"] = dict(delta_adapt=m, falsified=bool(not m[1] > 0))
    g = dd[(dd.organ == "W") & (dd.M == 1)]
    m = ci([h.retention.mean() for _, h in g.groupby("env")])
    R["E3e"] = dict(delta_retention=m, falsified=bool(not m[2] < 0))
    R["failure_effect_on_survival"] = dd.groupby("organ").survival.mean().round(4).to_dict()
    # ---- E4 heterogeneous units: mixtures of viable-with-margin configs (theorem partial_viable)
    rng = np.random.default_rng(es + 4); cells = runs = deaths = 0
    for e in draw_envs("F", nE, es + 5, held):
        eta = 0.1
        ok = [i for i, c in enumerate(CFGS) if formal(c, e)["viable"] and e["X"] - formal(c, e)["peak"] > eta * formal(c, e)["L1"]]
        if len(ok) < 2: continue
        U = CA[rng.choice(ok, size=(32, 20))]
        mt = run(e, seeds[: len(seeds) // 2], units=20, eta=eta, unit_cfgs=U)
        cells += 32; runs += mt["surv_seed"].size; deaths += int((1 - mt["surv_seed"]).sum())
    R["E4"] = dict(cells=cells, runs=runs, agg_deaths=deaths, falsified=bool(deaths > 0 or cells == 0))
    R["_meta"] = dict(mode=mode, seeds=[seeds[0], seeds[-1]], nE=nE, env_seed=es, heldout_ranges=held,
                      runtime_s=round(time.time() - t0, 1),
                      ext_sha256=hashlib.sha256(open(__file__, "rb").read()).hexdigest(),
                      base_sha256=hashlib.sha256(open(cs.__file__, "rb").read()).hexdigest())
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, f"coupled_ext_{mode}_results.json"), "w") as fh:
        json.dump(R, fh, indent=1, default=lambda o: o.item() if hasattr(o, "item") else str(o))
    import gzip
    with gzip.open(os.path.join(here, f"coupled_ext_{mode}_rows.json.gz"), "wt") as fh:
        json.dump(dict(res=res, ad=ad, comp=comp), fh, default=lambda o: o.item() if hasattr(o, "item") else str(o))
    for k in sorted(R):
        if k.startswith("E"):
            print(k, json.dumps(R[k], default=str)[:300])
    print("meta", R["_meta"])


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "dev")
