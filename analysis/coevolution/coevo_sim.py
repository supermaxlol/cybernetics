"""Co-evolution simulations, built on CoupledEndogenous.lean. Usage: python coevo_sim.py selftest|dev|confirm

E1 rate threshold under noise. Error e' = (1−η)e + v − u + s·ε, response |u| ≤ r, death when |e| > X.
   Policies:
     clip — the Lean policy u = clip_r((1−η)e + v);
     prop — a proportional controller u = clip_r(κ·((1−η)e + v)) with κ = 0.5.
   Lean: with s = 0, clip survives forever iff v ≤ r + ηX.
E2 depletion. S' = S + q − c + s_q·ε, q' = q − βc. Lean: β > 0 kills from any stock. Closed-form
   deterministic death time t*.
E3 arms race (cost of viability). The environment accelerates, v_t = v0 + a·t. The agent buys
   response capacity r_t = r0 + b·t at a cost of κ_r·r_t per step, from income I and reserve R0.
   Death when |e| > X or the reserve is below 0. The deterministic death time is computed by the
   same recursion with s = 0. The simulation adds noise.
E4 ultrastability (Ashby). The loop alternates between two regimes:
     A: one-step delay with g = 1. The Brake (k = kB) is needed; without it k = g gives resonance.
     B: no delay, with destabilising feedback δ. x' = (1 − k + δ)x + w, so the Brake (k = kB < δ) is fatal.
   Regime switches arrive at rate λ. Agents:
     fixed-Brake and fixed-no-Brake;
     ultrastable, which toggles the Brake whenever |x| > τ (after a switch it waits m_d steps
       before it may switch again);
     oracle, which knows the regime.
"""
import sys, os, json, math, itertools, hashlib, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))


# ---------------- E1 ----------------
def e1_cell(eta, r, X, s, ratio, policy, seeds, T=3000, key=0):
    v = ratio * (r + eta * X)
    rng = np.random.default_rng([key, 1])
    n = len(seeds)
    e = np.zeros(n); alive = np.ones(n, bool); ttd = np.full(n, T)
    eps = rng.standard_normal((T, n))
    for t in range(T):
        y = (1 - eta) * e + v
        u = np.clip(y if policy == "clip" else 0.5 * y, -r, r)
        e = np.where(alive, y - u + s * eps[t], e)
        d = alive & (np.abs(e) > X); ttd[d] = t + 1; alive &= ~d
    return dict(eta=eta, r=r, X=X, s=s, ratio=ratio, policy=policy, v=v, surv=float(alive.mean()), ttd=float(ttd.mean()))


# ---------------- E2 ----------------
def e2_tstar(S0, q0, c, beta, T):
    S, q = S0, q0
    for t in range(T):
        S = S + q - c; q = q - beta * c
        if S < 0: return t + 1
    return None


def e2_cell(S0, mu, c, beta, sq, seeds, T=20000, key=0):
    q0 = c * (1 + mu)
    rng = np.random.default_rng([key, 2]); n = len(seeds)
    S = np.full(n, float(S0)); q = q0; alive = np.ones(n, bool); ttd = np.full(n, T)
    for t in range(T):
        S = np.where(alive, S + q - c + sq * rng.standard_normal(n), S); q = q - beta * c
        d = alive & (S < 0); ttd[d] = t + 1; alive &= ~d
        if not alive.any(): break
    ts = e2_tstar(S0, q0, c, beta, T)
    return dict(S0=S0, mu=mu, c=c, beta=beta, sq=sq, surv=float(alive.mean()), ttd=float(ttd.mean()),
                tstar=ts, static_viable=q0 >= c)


# ---------------- E3 ----------------
def e3_run(a, b, s, n, T=20000, v0=0.05, r0=0.1, X=4.0, eta=0.05, I=0.05, kr=0.2, R0=20.0, key=0):
    rng = np.random.default_rng([key, 3])
    e = np.zeros(n); R = np.full(n, R0); alive = np.ones(n, bool); ttd = np.full(n, T); cause = np.zeros(n, int)
    for t in range(T):
        v = v0 + a * t; r = r0 + b * t
        y = (1 - eta) * e + v
        e = np.where(alive, y - np.clip(y, -r, r) + s * rng.standard_normal(n), e)
        R = np.where(alive, R + I - kr * r, R)
        d1 = alive & (np.abs(e) > X); d2 = alive & ~d1 & (R < 0)
        ttd[d1 | d2] = t + 1; cause[d1] = 1; cause[d2] = 2; alive &= ~(d1 | d2)
        if not alive.any(): break
    return ttd, cause


def e3_cell(a, b, s, seeds, key=0):
    t_det, c_det = e3_run(a, b, 0.0, 1, key=key)
    t, c = e3_run(a, b, s, len(seeds), key=key)
    return dict(a=a, b=b, s=s, ttd_det=int(t_det[0]), cause_det=int(c_det[0]), ttd=float(t.mean()),
                frac_budget=float((c == 2).mean()))


# ---------------- E4 ----------------
def e4_cell(lam, tau, md, s, seeds, T=3000, kB=0.25, delta=0.5, X=6.0, key=0):
    rng = np.random.default_rng([key, 4]); n = len(seeds)
    sw = rng.random((T, n)) < lam
    regA = np.cumsum(sw, axis=0) % 2 == 0           # start in A
    eps = s * rng.standard_normal((T, n))
    out = {}
    for agent in ("brake", "nobrake", "ultra", "oracle"):
        x = np.zeros(n); xp = np.zeros(n); alive = np.ones(n, bool); ttd = np.full(n, T)
        B = np.ones(n, bool) if agent != "nobrake" else np.zeros(n, bool)
        since = np.full(n, 10 ** 6); nsw = np.zeros(n)
        for t in range(T):
            A = regA[t]
            if agent == "oracle": B = A.copy()
            if agent == "ultra":
                flip = (np.abs(x) > tau) & (since >= md)
                B = np.where(flip, ~B, B); since = np.where(flip, 0, since + 1); nsw += flip
            k = np.where(B, kB, 1.0)
            xn = np.where(A, x - k * xp + eps[t], (1 - k + delta) * x + eps[t])
            xp = np.where(alive, x, xp); x = np.where(alive, xn, x)
            d = alive & (np.abs(x) > X); ttd[d] = t + 1; alive &= ~d
            if not alive.any(): break
        out[agent] = dict(surv=float(alive.mean()), ttd=float(ttd.mean()), switches=float(nsw.mean()))
    return dict(lam=lam, tau=tau, md=md, s=s, **out)


def selftest():
    # E1 with s = 0 is deterministic and must match the Lean threshold exactly
    for eta, r, X in itertools.product((0.0, 0.1), (0.1, 0.3), (2.0, 4.0)):
        for ratio in (0.9, 1.0, 1.1):
            c = e1_cell(eta, r, X, 0.0, ratio, "clip", [0], T=5000)
            assert (c["surv"] == 1.0) == (ratio <= 1.0), c
    # E2 deterministic: sim with sq = 0 equals the closed-form recursion
    c = e2_cell(10, 0.0, 0.1, 1e-3, 0.0, [0]); assert c["ttd"] == c["tstar"], c
    c = e2_cell(10, 0.2, 0.1, 0.0, 0.0, [0]); assert c["surv"] == 1.0 and c["tstar"] is None
    print("selftest OK: E1 threshold == Lean rate_iff at s=0; E2 == closed form")


def run(mode):
    t0 = time.time(); base = {"dev": 100, "confirm": 200}[mode]
    seeds = list(range({"dev": 100, "confirm": 200}[mode]))
    out = dict(mode=mode, script_sha256=hashlib.sha256(open(__file__, "rb").read()).hexdigest())
    ratios = [round(0.5 + 0.05 * i, 2) for i in range(21)]
    e1 = []; k = 0
    Xs = (4.0,) if mode == "dev" else (4.0, 6.0)          # confirm adds an out-of-sample tolerance
    for X, eta, r, s, pol in itertools.product(Xs, (0.0, 0.05, 0.15), (0.1, 0.3), (0.0, 0.05, 0.15, 0.3), ("clip", "prop")):
        for ra in ratios:
            k += 1; e1.append(e1_cell(eta, r, X, s, ra, pol, seeds, key=base * 10000 + k))
    out["e1"] = e1; print("e1", round(time.time() - t0))
    e2 = []
    cs = (0.1,) if mode == "dev" else (0.1, 0.2)
    for c, S0, mu, beta, sq in itertools.product(cs, (5, 20), (0.0, 0.1, 0.3), (0.0, 1e-4, 1e-3, 1e-2), (0.0, 0.05)):
        k += 1; e2.append(e2_cell(S0, mu, c, beta, sq, seeds, key=base * 10000 + k))
    out["e2"] = e2; print("e2", round(time.time() - t0))
    e3 = []
    As = (1e-4, 3e-4) if mode == "dev" else (1e-4, 2e-4, 3e-4)
    for a, b, s in itertools.product(As, (0.0, 0.5e-4, 1e-4, 2e-4, 3e-4, 5e-4), (0.05, 0.2)):
        k += 1; e3.append(e3_cell(a, b, s, seeds, key=base * 10000 + k))
    out["e3"] = e3; print("e3", round(time.time() - t0))
    e4 = []
    for lam, tau, md, s in itertools.product((1e-3, 3e-3, 1e-2, 3e-2), (0.5, 1, 2, 3, 4.5), (1, 5), (0.3,)):
        k += 1; e4.append(e4_cell(lam, tau, md, s, seeds, key=base * 10000 + k))
    out["e4"] = e4; print("e4", round(time.time() - t0))
    json.dump(out, open(os.path.join(HERE, f"coevo_{mode}_raw.json"), "w"), indent=1)
    print("wrote", mode, round(time.time() - t0))


if __name__ == "__main__":
    m = sys.argv[1] if len(sys.argv) > 1 else "selftest"
    selftest() if m == "selftest" else run(m)
