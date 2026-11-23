"""Stochastic coupled recursive viability: radCAD atlas, scaling, population and failure experiments.

This extends the shared-state model of FiveOrgans/Coupled.lean, as the earlier sims did. It
does not import the frozen scripts' engines. It imports only the frozen Lean mirror `formal()`
for a self-test.

State (one lane = one configuration x seed x unit)
  x, xp        shared state and its previous value
  m            slow memory: baseline estimate of the drift θ; EMA rate a_s (a_s = 0 is the
               Lean memory, frozen at θ0)
  acc, cnt     fast memory: the Watcher's window of the innovation w
  R            resource stock (one per unit, or one shared pool per population)
Step
  funded organs: by priority order, an organ runs this step only if the budget R + income
                 covers it (dynamic resource coupling)
  sf = σ^S α^P   shock attenuation (Skin, Spotlight)
  L  = 1 if P else K   Watcher latency (Spotlight shortens it)
  k  = kB if B else g  loop gain (Brake; g = unbraked feedback strength)
  w  = θ − m·M + sf·d + χ·mean_{j≠i} x_j          (χ = spillover between units)
  Watcher (needs M): window mean over L steps. It fires if |mean| > τ and it does not miss
     (probability q_miss), or it fires spuriously (probability q_fa) at any window end;
     on firing, m ← m + mean
  slow memory: m ← m + a_s·w
  delay: x' = x − k·xp + w      no delay: x' = (1−k)·x + w
  R ← R + income − funded cost − κ|x|
  death: |x| > X or R < 0
Shocks d: AR(1) with persistence ρ and unit-variance innovations drawn from a uniform,
Gaussian, Student-t5 or Student-t3 distribution, times the scale s = 1.
Drift θ: piecewise constant; shifts arrive at rate λ and the new level is U(−Θ, Θ).
All arms share each seed's exogenous paths (common random numbers).

Usage: python stoch_sim.py selftest | dev | confirm
"""
import sys, json, math, hashlib, itertools, time, os
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
CFGS = list(itertools.product([0, 1], repeat=5))          # (S, M, P, B, W)
NAMES = ["".join("SMPBW"[i] for i in range(5) if c[i]) or "-" for c in CFGS]
ORG = "SMPBW"
BLOCK = 100


# ============ worst-case projection (generalises the Lean rule FiveOrgans.Coupled.viable_closed) ============
def impulse(k, delay, n=4000):
    h = np.zeros(n)
    if delay:
        h[0] = 1.0
        if n > 1: h[1] = 1.0
        for t in range(2, n):
            h[t] = h[t - 1] - k * h[t - 2]
            if abs(h[t]) > 1e12: return None
    else:
        a = 1.0 - k
        if abs(a) >= 1: return None
        h = a ** np.arange(n)
    if abs(h[-50:]).max() > 1e-6: return None             # not stable (marginal or growing)
    return h


def wc_viable(c, e, D, kB=None):
    """Worst-case (adversarial, bounded-class) viability of configuration c in environment e.
    The class is |d| ≤ D (D = sup of the realised shocks), drift |θ| ≤ Θ, an adversarial Watcher
    miss whenever q_miss > 0, and organs always funded (cost + κX ≤ income).
    The memory projection uses the Lean semantics (frozen baseline)."""
    S, M, P, B, W = c
    kB = e["kB"] if kB is None else kB
    cost = sum(e["cost"][i] for i in range(5) if c[i])
    if cost + e["kappa"] * e["X"] > e["income"] + 1e-12:
        return False
    k = kB if B else e["g"]
    h = impulse(k, e["delay"])
    if h is None:
        return False
    a = np.abs(h)
    sf = (e["sigma"] if S else 1) * (e["alpha"] if P else 1)
    lat = 1 if P else e["K"]
    shift = e["lam"] > 0
    W_eff = W and e["q_miss"] == 0
    if M:
        dr = (2 * e["Theta"] * (a[:lat].sum() if W_eff else a.sum())) if shift else 0.0
    else:
        dr = e["Theta"] * a.sum()
    return bool(sf * D * a.sum() + dr <= e["X"] + 1e-9)


def selftest():
    """The generalised projection must reproduce the seven Lean ablation tables
    (CoupledAblation.lean). Setting: g = 1, kB = 1/4, perfect Watcher, cost 0.1 per organ."""
    def mk(D, Th, X, K, dl, sh, inc):
        return dict(Theta=Th, X=X, sigma=.5, alpha=.5, K=K, delay=dl, lam=.01 if sh else 0, income=inc,
                    g=1.0, kB=.25, q_miss=0, kappa=0, cost=[.1] * 5), D
    want = {"calm": (mk(1, 0, 1.5, 3, 0, 0, 1), 20), "delayE": (mk(1, 0, 4, 3, 1, 0, 1), 16),
            "shiftFast": (mk(1, 1, 4, 1, 1, 1, 1), 3), "shiftSlow": (mk(1, 1, 4, 4, 1, 1, 1), 2),
            "deadbeatShift": (mk(1, 1, 1.5, 3, 0, 1, 1), 6), "hostile": (mk(1, .25, 1.75, 3, 1, 1, 1), 1),
            "poor": (mk(1, .25, 1.75, 3, 1, 1, .4), 0)}
    sys.path.insert(0, os.path.join(HERE, "..", "coupled"))
    from coupled_sim import formal                       # frozen Lean mirror (read-only import)
    for name, ((e, D), n) in want.items():
        got = sum(wc_viable(c, e, D) for c in CFGS)
        assert got == n, (name, got, n)
        fe = dict(D=D, Theta=e["Theta"], X=e["X"], sigma=.5, alpha=.5, K=e["K"], delay=e["delay"],
                  shift=e["lam"] > 0, income=e["income"])
        for c in CFGS:
            assert wc_viable(c, e, D) == formal(c, fe)["viable"], (name, c)
    print("selftest OK: generalised worst-case projection == Lean tables (7 envs x 32 configs)")


# ============ exogenous paths ============
def shock_innov(r, dist, size):
    if dist == "uniform": return r.uniform(-math.sqrt(3), math.sqrt(3), size)
    if dist == "gauss": return r.standard_normal(size)
    if dist == "t5": return r.standard_t(5, size) / math.sqrt(5 / 3)
    if dist == "t3": return r.standard_t(3, size) / math.sqrt(3)
    raise ValueError(dist)


def ar1(eps, rho):
    if rho == 0: return eps
    out = np.empty_like(eps); out[..., 0] = eps[..., 0]
    c = math.sqrt(1 - rho * rho)
    for t in range(1, eps.shape[-1]):
        out[..., t] = rho * out[..., t - 1] + c * eps[..., t]
    return out


def paths(e, seed, N, T):
    r = np.random.default_rng([seed, e["key"]])
    th = np.empty(T)
    th0 = r.uniform(-e["Theta"], e["Theta"]); th[:] = th0
    t = 0
    if e["lam"] > 0:
        while True:
            t += int(r.geometric(e["lam"]))
            if t >= T: break
            th[t:] = r.uniform(-e["Theta"], e["Theta"])
    d = e.get("s", 1.0) * ar1(shock_innov(r, e["dist"], (N, T)), e["rho"])
    um = r.random((N, T)); uf = r.random((N, T))
    het = np.exp(e.get("het", 0.0) * r.standard_normal((N, 3)))   # multipliers on kB, sf, K
    return th, d, um, uf, het


# ============ vectorised engine: arms x seeds x units ============
class Engine:
    """arms: list of (cfg tuple, fail_organ or None, fail_time, unit_mask or None).
    unit_mask selects the units an arm's failure applies to (default: all units)."""

    def __init__(self, e, arms, seeds, N=1, T=1000, pool=False, exo=None):
        self.e, self.T, self.N, self.pool = e, T, N, pool
        nA, nS = len(arms), len(seeds)
        sh = (nA, nS, N); self.sh = sh
        base = np.zeros(sh + (5,), bool); self.fail = np.zeros(sh + (5,), bool)
        self.fail_t = np.full(sh, 10 ** 9); self.fail_org = np.full(sh, -1)
        for i, (c, fo, ft, um) in enumerate(arms):
            base[i] = np.array(c, bool)
            if fo is not None:
                j = ORG.index(fo); mask = np.ones(N, bool) if um is None else np.asarray(um)
                self.fail_org[i][:, mask] = j; self.fail_t[i][:, mask] = ft
        self.base = base
        P = [paths(e, s, N, T) for s in seeds] if exo is None else exo
        self.exo = P
        self.th = np.stack([p[0] for p in P]); self.d = np.stack([p[1] for p in P])
        self.um = np.stack([p[2] for p in P]); self.uf = np.stack([p[3] for p in P])
        het = np.stack([p[4] for p in P])                      # nS x N x 3
        self.kB = e["kB"] * het[None, :, :, 0]
        self.sig = np.minimum(e["sigma"] * het[None, :, :, 1], 1.0)
        self.alp = np.minimum(e["alpha"] * het[None, :, :, 1], 1.0)
        self.K = np.maximum(1, np.round(e["K"] * het[None, :, :, 2])).astype(int)
        self.cost = np.array(e["cost"])
        self.prio = [ORG.index(o) for o in e["prio"]]
        z = lambda: np.zeros(sh)
        self.x, self.xp, self.acc = z(), z(), z()
        self.cnt = np.zeros(sh, int)
        self.m = np.where(base[..., 1], self.th[None, :, 0, None], 0.0)
        self.R = np.full((nA, nS) if pool else sh, e["R0"] * (N if pool else 1))
        self.alive = np.ones(sh, bool); self.ttd = np.full(sh, T)
        self.funded_frac = z(); self.agg_dead = np.zeros((nA, nS), bool); self.agg_ttd = np.full((nA, nS), T)
        self.t = 0

    def funding(self, act):
        e = self.e
        if not self.pool:
            budget = self.R + e["income"]; used = np.zeros(self.sh); fund = np.zeros_like(act)
            for j in self.prio:
                ok = act[..., j] & (used + self.cost[j] <= budget)
                fund[..., j] = ok; used = used + np.where(ok, self.cost[j], 0)
            return fund, used
        # shared pool: units funded in index order, all-or-nothing per unit
        demand = (act * self.cost).sum(-1) * self.alive
        cum = np.cumsum(demand, axis=2)
        budget = (self.R + e["income"] * self.N)[..., None]
        okU = cum <= budget
        fund = act & okU[..., None]
        return fund, np.where(okU, demand, 0).sum(axis=2)

    def step(self):
        e, t = self.e, self.t
        a = self.alive if not e.get("zombie") else np.ones(self.sh, bool)   # zombie: failed units stay coupled
        failed = self.fail_t <= t
        act = self.base.copy()
        fo = self.fail_org
        for j in range(5):
            act[..., j] &= ~(failed & (fo == j))
        fund, used = self.funding(act & self.alive[..., None])   # failed units run no organs
        S_, M_, P_, B_, W_ = (fund[..., j] for j in range(5))
        sf = np.where(S_, self.sig, 1.0) * np.where(P_, self.alp, 1.0)
        L = np.where(P_, 1, self.K)
        k = np.where(B_, self.kB, e["g"])
        th = self.th[None, :, t, None]
        spill = 0.0
        if self.N > 1 and e.get("chi", 0) > 0:
            tot = self.x.sum(axis=2, keepdims=True)
            spill = e["chi"] * (tot - self.x) / (self.N - 1)
        # permanently failed memory loses its content
        lostM = failed & (fo == 1)
        self.m = np.where(lostM, 0.0, self.m)
        w = th - np.where(M_, self.m, 0.0) + sf * self.d[None, :, :, t] + spill
        # Watcher = fast memory window (needs M)
        wa = M_ & W_ & a
        self.acc += np.where(wa, w, 0); self.cnt += wa
        full = wa & (self.cnt >= L)
        mean = np.where(full, self.acc / np.maximum(self.cnt, 1), 0)
        tau = e["tau_c"] * sf
        fire = full & (((np.abs(mean) > tau) & (self.um[None, :, :, t] >= e["q_miss"]))
                       | (self.uf[None, :, :, t] < e["q_fa"]))
        self.m = np.where(fire, self.m + mean, self.m)
        self.acc = np.where(full | ~wa, 0, self.acc); self.cnt = np.where(full | ~wa, 0, self.cnt)
        # slow memory
        self.m = np.where(M_ & a, self.m + e["a_s"] * w, self.m)
        # shared loop
        xn = self.x - k * self.xp + w if e["delay"] else (1 - k) * self.x + w
        self.xp = np.where(a, self.x, self.xp); self.x = np.where(a, xn, self.x)
        dev = e["kappa"] * np.abs(self.x) * a
        if self.pool:
            self.R = self.R + e["income"] * self.N - used - dev.sum(axis=2)
            broke = np.broadcast_to((self.R < 0)[..., None], self.sh)
        else:
            self.R = np.where(a, self.R + e["income"] - used - dev, self.R)
            broke = self.R < 0
        self.funded_frac += np.where(a, (fund.sum(-1) == act.sum(-1)), 0)
        dead = self.alive & ((np.abs(self.x) > e["X"]) | broke)
        self.ttd = np.where(dead, t + 1, self.ttd); self.alive = self.alive & ~dead
        if self.N > 1:   # aggregate failure: |mean x| > X or more than half of the units dead
            ag = (np.abs(self.x.mean(axis=2)) > e["X"]) | ((~self.alive).mean(axis=2) > 0.5)
            nd = ag & ~self.agg_dead
            self.agg_ttd = np.where(nd, t + 1, self.agg_ttd); self.agg_dead |= ag
        self.t += 1


def run_radcad(e, arms, seeds, **kw):
    """Advance one environment with radCAD; each radCAD timestep runs BLOCK steps of the model."""
    from radcad import Model, Simulation, Experiment
    from radcad.engine import Engine as REngine, Backend
    holder = {}
    T = kw.get("T", 1000)

    def p_block(params, substep, sh, prev):
        sim = holder.setdefault("sim", Engine(e, arms, seeds, **kw))
        for _ in range(min(BLOCK, T - sim.t)):
            if not sim.alive.any():          # every lane dead: later steps change nothing
                sim.t = T; break
            sim.step()
        return {"t": sim.t}

    blocks = [{"policies": {"b": p_block}, "variables": {"t": lambda p, ss, sh, prev, pi: ("t", pi["t"])}}]
    model = Model(initial_state={"t": 0}, state_update_blocks=blocks, params={})
    sim = Simulation(model=model, timesteps=math.ceil(T / BLOCK), runs=1)
    exp = Experiment([sim])
    exp.engine = REngine(backend=Backend.SINGLE_PROCESS, deepcopy=False, drop_substeps=True)
    res = exp.run()
    assert res[-1]["t"] == T
    return holder["sim"]


# ============ Experiment A: atlas over the continuous parameter space ============
def draw_env(r, key):
    e = dict(key=key,
             dist=str(r.choice(["uniform", "gauss", "t5", "t3"])),
             rho=float(r.uniform(0, 0.9)) if r.random() < 0.5 else 0.0,
             Theta=float(r.uniform(0, 2)),
             lam=0.0 if r.random() < 0.3 else float(math.exp(r.uniform(math.log(5e-4), math.log(2e-2)))),
             q_miss=float(r.uniform(0, 0.5)) if r.random() < 0.7 else 0.0,
             q_fa=float(r.uniform(0, 0.05)) if r.random() < 0.5 else 0.0,
             K=int(r.integers(1, 13)), tau_c=float(r.uniform(0.5, 1.5)),
             delay=bool(r.random() < 0.5), g=float(r.uniform(0.7, 1.2)), kB=float(r.uniform(0.1, 0.5)),
             sigma=float(r.uniform(0.3, 0.9)), alpha=float(r.uniform(0.3, 0.9)),
             a_s=0.0 if r.random() < 0.5 else float(math.exp(r.uniform(math.log(1e-4), math.log(1e-2)))),
             income=float(r.uniform(0.2, 1.0)), kappa=float(r.uniform(0, 0.01)),
             X=float(r.uniform(2, 12)), R0=10.0,
             prio="BSPWM" if r.random() < 0.5 else "WMPSB")
    cs = float(r.uniform(0.03, 0.2))
    e["cost"] = [cs * float(r.uniform(0.5, 1.5)) for _ in range(5)]
    return e


ATLAS_ARMS = [(c, None, 0, None) for c in CFGS] + [((1, 1, 1, 1, 1), o, 500, None) for o in ORG]


def atlas_env(e, seeds, T=1000):
    sim = run_radcad(e, ATLAS_ARMS, seeds, N=1, T=T)
    alive = sim.alive[:, :, 0]; ttd = sim.ttd[:, :, 0]
    D = float(np.abs(sim.d).max())
    out = dict(env=e, D_wc=D,
               surv=alive[:32].mean(1).tolist(), ttd=ttd[:32].mean(1).tolist(),
               surv_seed=alive[:32].astype(int).tolist(),
               wc=[wc_viable(c, e, D) for c in CFGS],
               funded=(sim.funded_frac[:32, :, 0] / np.maximum(ttd[:32], 1)).mean(1).tolist())
    # mid-run failure arms: full config, organ o fails at T/2
    full = 31
    alive_mid = ttd[full] > T // 2
    out["fail"] = {}
    for i, o in enumerate(ORG):
        a = 32 + i
        base = alive_mid
        out["fail"][o] = dict(n_alive_mid=int(base.sum()),
                              surv=float(alive[a][base].mean()) if base.any() else None,
                              surv_ctrl=float(alive[full][base].mean()) if base.any() else None,
                              ttd_after=float(np.mean(ttd[a][base & ~alive[a]] - T // 2)) if (base & ~alive[a]).any() else None)
    return out


def classify(row, rho_cost=1.0, delta=0.05):
    """Three necessity notions for each organ in one environment."""
    surv = np.array(row["surv"]); wc = np.array(row["wc"]); e = row["env"]
    cost = np.array([sum(e["cost"][i] for i in range(5) if c[i]) for c in CFGS])
    V = surv - rho_cost * cost / e["income"]
    res = {}
    for j, o in enumerate(ORG):
        has = np.array([c[j] == 1 for c in CFGS])
        wc_nec = bool(wc[has].any() and not wc[~has].any())
        avg_gap = float(surv[has].max() - surv[~has].max())
        marg = float(np.mean([surv[i] - surv[CFGS.index(tuple(c[:j]) + (0,) + tuple(c[j + 1:]))]
                              for i, c in enumerate(CFGS) if c[j] == 1]))
        prac_gap = float(V[has].max() - V[~has].max())
        res[o] = dict(wc=wc_nec, avg=avg_gap >= delta, avg_gap=avg_gap, marg=marg,
                      prac=prac_gap >= delta, prac_gap=prac_gap)
    return res


# ============ Experiment B: diffusion scaling and Chebyshev bounds ============
def scaling_cell(X, a, rho, dist, seeds, key, T=20000):
    """No Brake under delay with g = 1, no drift, no organs; shock amplitude a. Returns mean ttd."""
    e = dict(key=key, dist=dist, rho=rho, Theta=0.0, lam=0.0, q_miss=0, q_fa=0, K=1, tau_c=1, delay=True,
             g=1.0, kB=.25, sigma=1, alpha=1, a_s=0, income=1, kappa=0, X=X, R0=10, prio="BSPWM",
             cost=[0] * 5, s=a)
    sim = run_radcad(e, [((0, 0, 0, 0, 0), None, 0, None)], seeds, N=1, T=T)
    ttd = sim.ttd[0, :, 0]
    return dict(X=X, a=a, rho=rho, dist=dist, mean_ttd=float(ttd.mean()), censored=float((ttd >= T).mean()),
                se=float(ttd.std(ddof=1) / math.sqrt(len(ttd))))


def f_res(rho):
    """AR(1) spectral density at the loop's resonance ω = π/3, relative to white noise."""
    return (1 - rho ** 2) / (1 - rho + rho ** 2)


def cheb_cell(cfg_brake, rho, seeds, key, n=300, cs=(1, 2, 3, 4, 6, 8)):
    """Exceedance frequency of |x_n| ≥ c against the Chebyshev bound s²Σh²/c² (and 4m s²/c² unbraked)."""
    e = dict(key=key, dist="gauss", rho=rho, Theta=0.0, lam=0.0, q_miss=0, q_fa=0, K=1, tau_c=1, delay=True,
             g=1.0, kB=.25, sigma=1, alpha=1, a_s=0, income=1, kappa=0, X=1e9, R0=10, prio="BSPWM", cost=[0] * 5)
    cfg = (0, 0, 0, 1, 0) if cfg_brake else (0, 0, 0, 0, 0)
    sim = Engine(e, [(cfg, None, 0, None)], seeds, N=1, T=n)
    for _ in range(n): sim.step()
    x = sim.x[0, :, 0]
    if cfg_brake:
        h = impulse(.25, True); s2h = float((h[:n] ** 2).sum())
    else:
        s2h = 4 * (n // 6) + float((impulse_raw(n) [6 * (n // 6):n] ** 2).sum())
    out = []
    for c in cs:
        out.append(dict(c=c, freq=float((np.abs(x) >= c).mean()), bound=min(1.0, s2h / c ** 2)))
    return dict(brake=cfg_brake, rho=rho, n=n, var_emp=float(x.var()), var_theory_iid=s2h, cells=out)


def impulse_raw(n):
    h = np.zeros(n); h[0] = 1
    if n > 1: h[1] = 1
    for t in range(2, n): h[t] = h[t - 1] - h[t - 2]
    return h


# ============ Experiment C: populations — resource competition, spillover, one unbraked unit ============
def pop_env(N, chi, het, ratio, key, zombie=False):
    c_cfg = 0.05 * 5
    return dict(key=key, dist="gauss", rho=0.0, Theta=0.5, lam=0.002, q_miss=0.0, q_fa=0.0, K=4, tau_c=1.0,
                delay=True, g=1.0, kB=.25, sigma=.5, alpha=.5, a_s=0.0, income=ratio * c_cfg, kappa=0.0,
                X=6.0, R0=2.0, prio="BSPWM", cost=[0.05] * 5, chi=chi, het=het, N=N, ratio=ratio,
                zombie=zombie)


def pop_cell(N, chi, het, ratio, seeds, key, T=1000, zombie=False):
    e = pop_env(N, chi, het, ratio, key, zombie)
    full = (1, 1, 1, 1, 1)
    one_bad = np.zeros(N, bool); one_bad[0] = True
    arms = [(full, None, 0, None), (full, "B", 0, one_bad)]
    sim = run_radcad(e, arms, seeds, N=N, T=T, pool=True)
    alive = sim.alive; ttd = sim.ttd
    res = dict(N=N, chi=chi, het=het, ratio=ratio, zombie=zombie)
    for i, nm in enumerate(["control", "one_unbraked"]):
        others = alive[i][:, 1:] if N > 1 else alive[i]
        u0dead = ~alive[i][:, 0]
        res[nm] = dict(alive_frac=float(alive[i].mean()), agg_surv=float((~sim.agg_dead[i]).mean()),
                       others_dead_frac=float((~others).mean()),
                       others_dead_given_u0dead=float((~others[u0dead]).mean()) if u0dead.any() else None,
                       u0_dead=float(u0dead.mean()),
                       cascade_span=float(np.median([(ttd[i][s][~alive[i][s]].max() - ttd[i][s][~alive[i][s]].min())
                                                     for s in range(ttd.shape[1]) if (~alive[i][s]).sum() >= 2]))
                       if any((~alive[i][s]).sum() >= 2 for s in range(ttd.shape[1])) else None)
    return res


# ============ drivers ============
def run(mode):
    t0 = time.time()
    base = {"dev": 1000, "confirm": 2000}[mode]
    n_env = {"dev": 200, "confirm": 600}[mode]
    seeds = list(range(base, base + 16))
    r = np.random.default_rng(base)
    atlas = []
    for i in range(n_env):
        e = draw_env(r, base * 10000 + i)
        atlas.append(atlas_env(e, seeds))
        if i % 50 == 0: print(f"atlas {i}/{n_env} {time.time()-t0:.0f}s", flush=True)
    for row in atlas:
        row["cls"] = {str(rc): classify(row, rho_cost=rc) for rc in (0.5, 1.0, 2.0)}
    # B: scaling
    sseeds = list(range(base, base + {"dev": 200, "confirm": 400}[mode]))
    grid = ([(X, a, 0.0, "gauss") for X in (4, 6, 8, 12) for a in (0.5, 1.0)] if mode == "dev" else
            [(X, a, rho, dist) for X in (5, 7, 10) for a in (0.5, 1.0)
             for rho, dist in ((0.0, "gauss"), (0.0, "uniform"), (0.0, "t5"), (0.5, "gauss"), (0.8, "gauss"))])
    scaling = [scaling_cell(X, a, rho, dist, sseeds, base * 100 + i) for i, (X, a, rho, dist) in enumerate(grid)]
    print(f"scaling done {time.time()-t0:.0f}s", flush=True)
    cseeds = list(range(base, base + 4000))
    cheb = [cheb_cell(b, rho, cseeds, base * 7 + i) for i, (b, rho) in
            enumerate([(True, 0.0), (False, 0.0), (True, 0.5), (True, 0.8)])]
    # C: populations
    pseeds = list(range(base, base + 48))
    pop = []
    for i, (N, chi, het, ratio, zb) in enumerate(itertools.product((4, 8, 16), (0.0, 0.2, 0.5, 0.8), (0.0, 0.3),
                                                                   (0.5, 0.75, 1.0, 1.5), (False, True))):
        pop.append(pop_cell(N, chi, het, ratio, pseeds, base * 1000 + i, zombie=zb))
    print(f"pop done {time.time()-t0:.0f}s", flush=True)
    out = dict(mode=mode, script_sha256=hashlib.sha256(open(__file__, "rb").read()).hexdigest(),
               n_env=n_env, seeds=len(seeds), atlas=atlas, scaling=scaling, cheb=cheb, pop=pop,
               seconds=time.time() - t0)
    with open(os.path.join(HERE, f"stoch_{mode}_raw.json"), "w") as f:
        json.dump(out, f)
    print(f"wrote stoch_{mode}_raw.json in {time.time()-t0:.0f}s")


if __name__ == "__main__":
    m = sys.argv[1] if len(sys.argv) > 1 else "selftest"
    if m == "selftest":
        selftest()
    else:
        selftest(); run(m)
