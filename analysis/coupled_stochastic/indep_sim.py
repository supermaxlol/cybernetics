"""Independent check of stoch_sim.py.

1. A scalar, one-lane-at-a-time reimplementation of the step rule, written from the spec in the
   docstring of stoch_sim.py and in PREREG_stochastic_2026-11-23.md. It does not use the
   Engine class. It shares only the exogenous paths (drift, shocks, Watcher coin flips), so any
   disagreement points to an implementation error in one of the two codes.
2. Analytic variances (exact covariance sums), checked against the simulated variances in the
   Chebyshev cells:
     Var(x_n) = s² Σ_{u,v<n} h_u h_v ρ^{|u−v|}     (AR(1) shocks with unit variance)
   For ρ = 0 this is the Lean theorem var_resp_eq (CoupledStochastic.lean).

Usage: python indep_sim.py dev|confirm
"""
import sys, os, json, math
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import stoch_sim as ss          # used for: paths(), draw_env(), Engine (the code under test)

ORG = "SMPBW"


def scalar_lane(e, cfg, fail_org, fail_t, th, d, um, uf, het, T):
    S, M, P, B, W = cfg
    kB = e["kB"] * het[0]
    sig = min(e["sigma"] * het[1], 1.0); alp = min(e["alpha"] * het[1], 1.0)
    K = max(1, int(round(e["K"] * het[2])))
    x = xp = acc = 0.0; cnt = 0
    m = th[0] if M else 0.0
    R = e["R0"]
    for t in range(T):
        on = [S, M, P, B, W]
        if fail_org is not None and t >= fail_t:
            on[ORG.index(fail_org)] = 0
            if fail_org == "M": m = 0.0
        # funding by priority
        budget = R + e["income"]; used = 0.0; f = [0] * 5
        for o in e["prio"]:
            j = ORG.index(o)
            if on[j] and used + e["cost"][j] <= budget:
                f[j] = 1; used += e["cost"][j]
        fS, fM, fP, fB, fW = f
        sf = (sig if fS else 1.0) * (alp if fP else 1.0)
        L = 1 if fP else K
        k = kB if fB else e["g"]
        w = th[t] - (m if fM else 0.0) + sf * d[t]
        if fM and fW:
            acc += w; cnt += 1
            if cnt >= L:
                mean = acc / cnt
                if (abs(mean) > e["tau_c"] * sf and um[t] >= e["q_miss"]) or uf[t] < e["q_fa"]:
                    m += mean
                acc = 0.0; cnt = 0
        else:
            acc = 0.0; cnt = 0
        if fM:
            m += e["a_s"] * w
        xn = x - k * xp + w if e["delay"] else (1 - k) * x + w
        xp, x = x, xn
        R = R + e["income"] - used - e["kappa"] * abs(x)
        if abs(x) > e["X"] or R < 0:
            return t + 1
    return T


def agreement(n_env, seeds, key0, T=1000):
    r = np.random.default_rng(key0)
    tot = same = 0; worst = []
    for i in range(n_env):
        e = ss.draw_env(r, key0 * 1000 + i)
        sim = ss.Engine(e, ss.ATLAS_ARMS, seeds, N=1, T=T)
        for _ in range(T): sim.step()
        for si, sd in enumerate(seeds):
            th, d, um, uf, het = sim.exo[si]
            for ai, (cfg, fo, ft, _) in enumerate(ss.ATLAS_ARMS):
                t_ind = scalar_lane(e, cfg, fo, ft, th, d[0], um[0], uf[0], het[0], T)
                t_vec = int(sim.ttd[ai, si, 0])
                tot += 1; same += t_ind == t_vec
                if t_ind != t_vec: worst.append((i, sd, ss.NAMES[ai] if ai < 32 else "fail" + fo, t_ind, t_vec))
    return dict(lanes=tot, identical=same, frac=same / tot, mismatches=worst[:20])


def var_exact(h, rho, n):
    h = h[:n][::-1]                         # coefficient on shock j is h[n-1-j]
    idx = np.arange(n)
    C = rho ** np.abs(idx[:, None] - idx[None, :]) if rho > 0 else np.eye(n)
    return float(h @ C @ h)


def main(mode):
    base = {"dev": 31, "confirm": 47}[mode]
    ag = agreement({"dev": 10, "confirm": 30}[mode], list(range(base, base + 4)), base)
    print("agreement", ag["identical"], "/", ag["lanes"])
    raw = json.load(open(os.path.join(HERE, f"stoch_{mode}_raw.json")))
    var = []
    for c in raw["cheb"]:
        n = c["n"]
        h = ss.impulse(.25, True) if c["brake"] else ss.impulse_raw(n)
        ve = var_exact(np.asarray(h, float), c["rho"], n)
        var.append(dict(brake=c["brake"], rho=c["rho"], var_sim=c["var_emp"], var_exact=ve,
                        rel_err=abs(c["var_emp"] - ve) / ve))
        print(var[-1])
    out = dict(agreement=ag, variance=var)
    json.dump(out, open(os.path.join(HERE, f"indep_{mode}.json"), "w"), indent=1)


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "dev")
