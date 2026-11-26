"""Sensor scrambling with thresholds predicted beforehand. Usage: python sense.py dev SEED | confirm SEED | score
World: x' = a x + u + w, |w| <= d, death when |x| > 1, T steps. Four (a, d) cells.
S1 sensor reports one of M messages; arms: theory (uniform cells), learned without memory, learned with one message of memory.
S2 reading y = x + e, e ~ U(-s, s); arms: linear (u = -a y), learned without memory, learned observer (with memory).
S3 reading replaced by U(-1, 1) with probability eta; same arms as S2.
S4 emergence world (analysis/emergence/emerge.py, imported, not edited), error added to its sensor.
Learned arms: evolved tables or small controllers, fitness = mean fraction of life; they are not told a, d or any threshold.
Predictions use a and d only: M* = ceil(a/(1-d)), s_c = (1-d)/a, and closed-form survival of the linear rule."""
import sys, os, json, math, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(HERE, "..", "emergence"))
CELLS = {"A": (2.0, .25), "B": (1.2, .1), "C": (3.0, .2), "D": (4.0, .3)}
T, P, L, GENS = 200, 64, 64, 150
MSTAR = {c: math.ceil(a / (1 - d) - 1e-9) for c, (a, d) in CELLS.items()}
SC = {c: (1 - d) / a for c, (a, d) in CELLS.items()}
MULT = (.6, .8, .9, 1.0, 1.05, 1.1, 1.2, 1.3, 1.4, 1.7, 2.0)
ETA = (0., .0025, .005, .01, .02, .04, .08)


def noise(rng, d, T, L, kind):
    return rng.uniform(-d, d, (T, L)) if kind == "uni" else d * rng.choice([-1., 1.], (T, L))


# ---------- S1: message tables. theta (P, C, M-1) sorted, act (P, C, M); C = M contexts with memory, 1 without
def sim_tab(th, ac, a, d, T, L, rng, kind, rec=False):
    P, C, M = ac.shape; x = np.broadcast_to(rng.uniform(-1, 1, L), (P, L)).copy(); w = noise(rng, d, T, L, kind)
    m = np.zeros((P, L), int); alive = np.ones((P, L), bool); life = np.zeros((P, L)); I = np.arange(P)[:, None]; H = []
    for t in range(T):
        c = m if C > 1 else 0
        mo, m = m, ((x[:, :, None] > th[I, c]).sum(-1) if M > 1 else np.zeros((P, L), int))
        u = ac[I, c, m]
        if rec and t > 20: H.append((mo[0][alive[0]], m[0][alive[0]]))
        x = a * x + u + w[t]; alive &= np.abs(x) <= 1; life += alive; x = np.where(alive, x, 0.)
    return (life / T, alive, H) if rec else (life / T, alive)


def uni_tab(a, M):
    e = np.linspace(-1, 1, M + 1); c = (e[1:] + e[:-1]) / 2
    return e[1:-1][None, None], (-a * c)[None, None]


def evo(init, mut, fit, rng):
    G = init(rng)
    for g in range(GENS):
        f = fit(G, rng); o = np.argsort(-f)[:P // 4]; par = np.concatenate([o[:2], rng.choice(o, P - 2)])
        G = {k: v[par] for k, v in G.items()}; H = mut(G, rng, .3 * .02 ** (g / GENS))
        for k in H: H[k][:2] = G[k][:2]
        G = H
    f = sum(fit(G, rng) for _ in range(4)); b = int(np.argmax(f)); return {k: v[b:b + 1] for k, v in G.items()}


def learn_tab(a, d, M, mem, rng):
    C = M if mem else 1
    init = lambda r: dict(th=np.sort(r.uniform(-1, 1, (P, C, M - 1)), -1), ac=r.normal(0, 1, (P, C, M)))
    def mut(G, r, s):
        return dict(th=np.sort(G["th"] + s * r.normal(0, 1, G["th"].shape) * (r.random(G["th"].shape) < .4), -1),
                    ac=G["ac"] + s * a * r.normal(0, 1, G["ac"].shape) * (r.random(G["ac"].shape) < .4))
    return evo(init, mut, lambda G, r: sim_tab(G["th"], G["ac"], a, d, T, L, r, "bang")[0].mean(1), rng)


def invariant(th, ac, a, d, N=4001):
    """Largest set of (context, x) from which every bounded disturbance is survived (grid; conservative to one grid step)."""
    C, M = ac.shape[1:]; g = np.linspace(-1, 1, N); h = g[1] - g[0]
    m = np.stack([(g[:, None] > th[0, c]).sum(1) if M > 1 else np.zeros(N, int) for c in range(C)])
    lo = np.stack([a * g + ac[0, c, m[c]] - d for c in range(C)]); hi = lo + 2 * d
    ok = (lo >= -1 - 1e-9) & (hi <= 1 + 1e-9); nc = m if C > 1 else np.zeros_like(m)
    il = np.clip(np.ceil((lo + 1) / h - 1e-6).astype(int), 0, N - 1); ih = np.clip(np.floor((hi + 1) / h + 1e-6).astype(int), 0, N - 1)
    while True:
        cs = np.concatenate([np.zeros((C, 1), int), np.cumsum(~ok, 1)], 1)
        new = ok & (cs[nc, ih + 1] - cs[nc, np.minimum(il, ih + 1)] == 0)
        if (new == ok).all(): return float(ok[0].mean())
        ok = new


def ent_bits(H):
    if not H: return None
    mo = np.concatenate([h[0] for h in H]); m = np.concatenate([h[1] for h in H])
    if len(m) == 0: return None
    e = lambda z: float(-sum(p * np.log2(p) for p in np.unique(z, return_counts=True)[1] / len(z)))
    return dict(H=round(e(m), 3), Hcond=round(e(mo * 100 + m) - e(mo), 3))


def s1(cell, seed):
    a, d = CELLS[cell]; out = {}
    for M in range(max(1, MSTAR[cell] - 2), MSTAR[cell] + 3):
        rng = np.random.default_rng([seed, 1, ord(cell), M]); row = {}
        th, ac = uni_tab(a, M); arms = {"theory": dict(th=th, ac=ac), "learn": learn_tab(a, d, M, False, rng)}
        if M > 1: arms["mem"] = learn_tab(a, d, M, True, rng)
        for k, G in arms.items():
            r = lambda kd: sim_tab(G["th"], G["ac"], a, d, T, 2000, np.random.default_rng([seed, 2, ord(cell), M]), kd, True)
            b = r("bang"); n = r("uni")
            row[k] = dict(bang=float(b[1].mean()), uni=float(n[1].mean()), inv=invariant(G["th"], G["ac"], a, d), bits=ent_bits(n[2]))
        out[M] = row
    return out


# ---------- S2, S3: continuous reading
def sim_lin(G, a, d, T, L, rng, s, eta, kind="uni"):
    P = len(G["g"]); x = np.broadcast_to(rng.uniform(-1, 1, L), (P, L)).copy(); w = noise(rng, d, T, L, kind)
    e = rng.uniform(-s, s, (T, L)) if s > 0 else np.zeros((T, L)); rep = rng.random((T, L)) < eta; rv = rng.uniform(-1, 1, (T, L))
    xh = np.zeros((P, L)); up = np.zeros((P, L)); alive = np.ones((P, L), bool); life = np.zeros((P, L)); g = {k: v for k, v in G.items()}
    for t in range(T):
        y = np.where(rep[t], rv[t], x + e[t]); pred = g["p1"] * xh + g["p2"] * up; inn = y - pred
        xh = pred + g["p0"] * np.where(np.abs(inn) < np.abs(g["c"]), inn, 0.)
        u = g["g"] * xh + (g["v"][:, None, :] * np.tanh(xh[:, :, None] * g["b"][:, None, :] + g["o"][:, None, :])).sum(-1)
        up = u; x = a * x + u + w[t]; alive &= np.abs(x) <= 1; life += alive
        x = np.where(alive, x, 0.); xh = np.clip(xh, -5, 5); up = np.clip(up, -20, 20)
    return life / T, alive


def lin_rule(a):
    z = np.zeros((1, 4)); o = np.ones((1, 1)); return dict(g=-a * o, p0=o, p1=0 * o, p2=0 * o, c=99 * o, v=z, b=z, o=z)


def learn_lin(a, d, mem, rng, s, eta):
    def init(r):
        G = dict(g=r.normal(0, 1, (P, 1)), p0=np.ones((P, 1)), p1=np.zeros((P, 1)), p2=np.zeros((P, 1)), c=99 * np.ones((P, 1)),
                 v=r.normal(0, .2, (P, 4)), b=r.normal(0, 2, (P, 4)), o=r.normal(0, 1, (P, 4)))
        if mem: G["p1"] = r.normal(0, .5, (P, 1)); G["p2"] = r.normal(0, .5, (P, 1)); G["c"] = 2 * np.ones((P, 1))
        return G
    sc = dict(g=a, p0=.5, p1=a / 2, p2=.5, c=1., v=.5, b=2., o=1.)
    frozen = () if mem else ("p0", "p1", "p2", "c")
    def mut(G, r, q): return {k: v.copy() if k in frozen else v + q * sc[k] * r.normal(0, 1, v.shape) * (r.random(v.shape) < .4) for k, v in G.items()}
    return evo(init, mut, lambda G, r: sim_lin(G, a, d, T, L, r, s, eta)[0].mean(1), rng)


def closed(a, d, s):
    """Survival of u = -a y to T, starting in range: (1 - P(|a e + w| > 1))^T, e ~ U(-s,s), w ~ U(-d,d)."""
    if s == 0: return 1.0
    n = 20000; e = (np.arange(n) + .5) / n * s; lim = (1 - a * e)          # dies if w > lim (by symmetry both signs equal)
    p = np.clip((d - lim) / (2 * d), 0, 1).mean(); return float((1 - p) ** T)


def s50(xs, ys):
    for i in range(1, len(xs)):
        if ys[i] < .5 <= ys[i - 1]: return xs[i - 1] + (xs[i] - xs[i - 1]) * (ys[i - 1] - .5) / (ys[i - 1] - ys[i])
    return xs[-1] if ys[-1] >= .5 else xs[0]


def operator(a, d, eta, N=801):
    """Survival of the linear rule when the reading is U(-1,1) with probability eta (transfer operator on a grid)."""
    g = (np.arange(N) + .5) / N * 2 - 1; h = 2 / N; w = np.clip((d + h / 2 - np.abs(g)) / h, 0, 1); w = w / w.sum()   # clean step: x' = w
    # corrupted step: x' = a (x - y) + w
    Z = np.linspace(-a * 2 - d, a * 2 + d, 2001)
    ys = (np.arange(400) + .5) / 200 - 1; ws = ((np.arange(40) + .5) / 20 - 1) * d
    off = (-a * ys[:, None] + ws[None]).ravel(); hst, ed = np.histogram(off, bins=1200); dens = hst / hst.sum(); ce = (ed[1:] + ed[:-1]) / 2
    K = np.zeros((N, N))
    for i, x in enumerate(g):
        z = a * x + ce; k = np.abs(z) <= 1; K[i] = np.bincount(np.clip(((z[k] + 1) / h).astype(int), 0, N - 1), weights=dens[k], minlength=N)
    q = np.ones(N) / N
    for t in range(T): q = (1 - eta) * q.sum() * w + eta * (q @ K)
    return float(q.sum())


def s23(cell, seed):
    a, d = CELLS[cell]; o2, o3 = {}, {}
    for k in MULT:
        s = k * SC[cell]; rng = np.random.default_rng([seed, 3, ord(cell), int(k * 100)])
        arms = dict(linear=lin_rule(a), learn=learn_lin(a, d, False, rng, s, 0.), mem=learn_lin(a, d, True, rng, s, 0.))
        o2[k] = {n: float(sim_lin(G, a, d, T, 4000, np.random.default_rng([seed, 4, ord(cell), int(k * 100)]), s, 0.)[1].mean()) for n, G in arms.items()}
        o2[k]["closed"] = closed(a, d, s)
    for eta in ETA:
        rng = np.random.default_rng([seed, 5, ord(cell), int(eta * 1e4)])
        arms = dict(linear=lin_rule(a), learn=learn_lin(a, d, False, rng, 0., eta), mem=learn_lin(a, d, True, rng, 0., eta))
        o3[eta] = {n: float(sim_lin(G, a, d, T, 4000, np.random.default_rng([seed, 6, ord(cell), int(eta * 1e4)]), 0., eta)[1].mean()) for n, G in arms.items()}
        o3[eta]["operator"] = operator(a, d, eta)
    return o2, o3


# ---------- S4: the emergence world, class 9 = no extra pressure, sensor error U(-s, s)
def s4(seed):
    import emerge as E
    out = {}
    for s in (0., 2., 3., 4., 5., 6., 8., 12.):
        row = {}
        for arm in ("full", "five"):
            rng = np.random.default_rng([seed, 7, int(s * 10), len(arm)]); PP, LL = 60, 32; cl = np.full(LL, 9); act = E.five_act if arm == "five" else E.net_act
            def hook(r, L):
                def ab(o): o = o.copy(); o[..., 0] += r.uniform(-s, s, L) if s > 0 else 0.; return o
                return ab
            G = E.new(arm, PP, rng)
            for g in range(50):
                f = E.simulate(act(G), E.st0(arm, PP, LL), E.world(cl, rng, E.T, PP, LL), PP, LL, E.T, hook(rng, LL))[0].mean(1)
                top = np.argsort(-f)[:PP // 4]; par = np.concatenate([top[:2], rng.choice(top, PP - 2)])
                ch = {k: v[par] for k, v in G.items()}; m = E.mutate(arm, ch, rng)
                for k in m: m[k][:2] = ch[k][:2]
                G = m
            f = E.simulate(act(G), E.st0(arm, PP, 200), E.world(np.full(200, 9), rng, E.T, PP, 200), PP, 200, E.T, hook(rng, 200))[0].mean(1); b = int(np.argmax(f))
            r2 = np.random.default_rng([seed, 8, int(s * 10)]); Gb = {k: v[b:b + 1] for k, v in G.items()}
            lf = E.simulate(act(Gb), E.st0(arm, 1, 1000), E.world(np.full(1000, 9), r2, E.T, 1, 1000), 1, 1000, E.T, hook(r2, 1000))[0]
            row[arm] = float((lf >= 1 - 1e-9).mean())
        out[s] = row
    return out


def run(seed, cells="ABCD4"):
    o = dict(s1={}, s2={}, s3={}, seed=seed)
    for c in cells.replace("4", ""):
        t = time.time(); o["s1"][c] = s1(c, seed); o["s2"][c], o["s3"][c] = s23(c, seed); print(c, round(time.time() - t), "s", flush=True)
    if "4" in cells: t = time.time(); o["s4"] = s4(seed); print("s4", round(time.time() - t), flush=True)
    return o


def show(o):
    for c in o["s1"]:
        a, d = CELLS[c]; print(f"== {c} a={a} d={d} M*={MSTAR[c]} (exact {a/(1-d):.2f}) s_c={SC[c]:.3f}")
        for M, r in o["s1"][c].items(): print("  M", M, {k: (round(v["bang"], 3), round(v["uni"], 3), round(v["inv"], 3), v["bits"]) for k, v in r.items()})
        for k, r in o["s2"][c].items(): print("  s/s_c", k, {n: round(v, 3) for n, v in r.items()})
        for k, r in o["s3"][c].items(): print("  eta", k, {n: round(v, 3) for n, v in r.items()})
    if "s4" in o: print("s4", {s: {k: round(v, 3) for k, v in r.items()} for s, r in o["s4"].items()})


if __name__ == "__main__":
    if sys.argv[1] in ("dev", "confirm"):
        cells = sys.argv[3] if len(sys.argv) > 3 else "ABCD4"; o = run(int(sys.argv[2]), cells)
        json.dump(o, open(os.path.join(HERE, f"{sys.argv[1]}_{sys.argv[2]}_{cells}.json"), "w"), indent=1); show(o)
