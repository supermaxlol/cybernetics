"""Real environments, simulated agent. Usage: python real_env.py dev|confirm

The environment is real; the agent is simulated. This is NOT a test on a real organisation. Two FRED
daily series (VIXCLS, DTWEXBGS, 2018-01 to 2026-07) supply the disturbance path that the agent must
absorb. The agent is the stoch_sim Engine.

  u_t = Δlog y_t / sd_1(Δlog y)    (sd_1 from the FIRST half only)
  θ_t = trailing 20-day mean of u  (slowly varying drift; what Memory and Watcher can learn)
  d_t = u_t − θ_t                  (fast shock; what Skin and Spotlight attenuate)

Each series is split in time. Half 1 is used for calibration and selection; half 2 is the held-out test.
Watcher coin flips are the only randomness (16 seeds); the environment path is fixed.

dev     runs the tests on the first 60% of half 1 (calibration) against the last 40% of half 1.
        It never reads half 2.
confirm runs half 1 against half 2.

Tests (thresholds in PREREG_stochastic_2026-11-23.md, H13a-d):
  a  ranking stability: median Spearman over agent envs of the 32-config survival vectors, calib vs test
  b  Brake sign transfer: Brake marginal > 0 under delay with g >= 1, and < 0 without delay, on the test path
  c  diffusion prediction: no-organ delay g=1 loop with restart. The mean inter-failure interval on the
     test path is predicted from calibration (a², ρ̂) by C·X²/(a² f(ρ̂)), C = analyze.CONST
  d  capacity prescription: the cheapest config with survival ≥ 0.9 on calibration still has
     survival ≥ 0.9 on the test path
"""
import sys, os, json, itertools, math, hashlib
import numpy as np
from scipy import stats
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import stoch_sim as ss
from analyze import CONST

DATA = os.path.expanduser("~/Desktop/upifailurebangladesh/data")
SERIES = ("VIXCLS", "DTWEXBGS")
ORG = "SMPBW"
CFGS = ss.CFGS


def load(name):
    p = os.path.join(DATA, f"fred_{name}.csv")
    v = []
    for ln in open(p).read().splitlines()[1:]:
        a, b = ln.split(",")
        if b not in ("", "."): v.append(float(b))
    return np.array(v), hashlib.sha256(open(p, "rb").read()).hexdigest()


def env_paths(y, sd):
    r = np.diff(np.log(y)) / sd
    th = np.array([r[max(0, t - 20):t].mean() if t > 0 else 0.0 for t in range(len(r))])
    return th, r - th


def split(y, mode):
    h = len(y) // 2
    if mode == "confirm": return y[:h + 1], y[h:]
    c = int(0.6 * h); return y[:c + 1], y[c:h + 1]


def agent_grid():
    for delay, g, K, a_s, X in itertools.product((True, False), (0.9, 1.0, 1.1), (2, 6, 10), (0.0, 0.003), (4.0, 6.0, 8.0)):
        yield dict(key=0, delay=delay, g=g, kB=0.25, sigma=0.5, alpha=0.5, K=K, tau_c=0.5, q_miss=0.2, q_fa=0.02,
                   a_s=a_s, X=X, R0=10.0, income=0.5, kappa=0.0, cost=[0.05] * 5, prio="BSPWM")


def run_env(e, th, d, seeds):
    T = len(th)
    P = []
    for s in seeds:
        r = np.random.default_rng([s, 777])
        P.append((th, d[None, :], r.random((1, T)), r.random((1, T)), np.ones((1, 3))))
    arms = [(c, None, 0, None) for c in CFGS]
    sim = ss.Engine(e, arms, seeds, N=1, T=T, exo=P)
    for _ in range(T):
        sim.step()
        if not sim.alive.any(): break
    return sim.alive[:, :, 0].mean(1)


def marg(s, j):
    return float(np.mean([s[i] - s[CFGS.index(c[:j] + (0,) + c[j + 1:])] for i, c in enumerate(CFGS) if c[j]]))


def restart_ttd(w, X):
    """No organs, delay, g = 1: x' = x − x_prev + w. On |x| > X record the interval and reset to 0."""
    x = xp = 0.0; last = 0; iv = []
    for t, wt in enumerate(w):
        x, xp = x - xp + wt, x
        if abs(x) > X:
            iv.append(t + 1 - last); last = t + 1; x = xp = 0.0
    return iv


def main(mode):
    seeds = list(range(16)); out = dict(mode=mode, series={})
    for name in SERIES:
        y, sha = load(name)
        cal, tst = split(y, mode)
        sd = float(np.std(np.diff(np.log(cal))))
        thc, dc = env_paths(cal, sd); tht, dt = env_paths(tst, sd)
        rows = []
        for e in agent_grid():
            sc = run_env(e, thc, dc, seeds); st = run_env(e, tht, dt, seeds)
            rows.append(dict(env={k: e[k] for k in ("delay", "g", "K", "a_s", "X")}, cal=sc.tolist(), test=st.tolist()))
        # a ranking stability
        rh = [stats.spearmanr(r["cal"], r["test"])[0] for r in rows if np.std(r["cal"]) > 0 and np.std(r["test"]) > 0]
        # b Brake sign
        B = ORG.index("B")
        bd = [marg(r["test"], B) for r in rows if r["env"]["delay"] and r["env"]["g"] >= 1]
        bn = [marg(r["test"], B) for r in rows if not r["env"]["delay"]]
        # c diffusion prediction
        wc = thc + dc; wt = tht + dt
        a2 = float(np.var(wc)); rho = float(np.corrcoef(wc[:-1], wc[1:])[0, 1])
        pred = []
        for X in (4.0, 6.0, 8.0):
            iv = restart_ttd(wt, X)
            p = CONST * X ** 2 / (a2 * ss.f_res(rho))
            pred.append(dict(X=X, n_failures=len(iv), obs=float(np.mean(iv)) if iv else None, pred=p,
                             ratio=(float(np.mean(iv)) / p) if iv else None))
        # d capacity prescription
        presc = []
        for r in rows:
            ok = [(sum(c), i) for i, c in enumerate(CFGS) if r["cal"][i] >= 0.9]
            if not ok: continue
            i = min(ok)[1]
            presc.append(dict(env=r["env"], cfg="".join(o for o, b in zip(ORG, CFGS[i]) if b) or "-", test_surv=r["test"][i]))
        out["series"][name] = dict(
            sha256=sha, n_cal=len(cal), n_test=len(tst), sd_cal=sd, a2_cal=a2, rho_cal=rho,
            a2_test=float(np.var(wt)), rho_test=float(np.corrcoef(wt[:-1], wt[1:])[0, 1]),
            kurt_cal=float(stats.kurtosis(wc)),
            Ha_median_spearman=float(np.median(rh)) if rh else None, Ha_n=len(rh),
            Hb_brake_delay=float(np.mean(bd)), Hb_brake_nodelay=float(np.mean(bn)),
            Hc=pred, Hd_n=len(presc), Hd_hold=float(np.mean([p["test_surv"] >= 0.9 for p in presc])) if presc else None,
            Hd_examples=presc[:12], rows=rows)
        s = out["series"][name]
        s["Ha_pass"] = s["Ha_median_spearman"] is not None and s["Ha_median_spearman"] > 0.5
        s["Hb_pass"] = s["Hb_brake_delay"] > 0 and s["Hb_brake_nodelay"] < 0
        s["Hc_pass"] = all(p["ratio"] is not None and 0.5 <= p["ratio"] <= 2.0 for p in pred)
        s["Hd_pass"] = s["Hd_hold"] is not None and s["Hd_hold"] >= 0.7
        print(name, {k: v for k, v in s.items() if k not in ("rows", "Hd_examples")})
    json.dump(out, open(os.path.join(HERE, f"real_{mode}.json"), "w"), indent=1)


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "dev")
