"""Do five-organ functions emerge in evolved controllers? Usage: python emerge.py dev SEED | confirm SEED | score
World: one unstable scalar, |x| <= X or death. Inputs: y, z1, z2, cue, previous action, 1. Outputs: u and a shield g.
Classes (each a pressure): 0 noise (z1 is the shared sensor noise, z2 pure distraction), 1 hidden actuator sign with a
one-step cue, 2 lying sensor, 3 bursts (a shield helps), 4 actuation delay, 5 reactive (noise grows with own action).
Arms: emerge (structure + weights, upkeep), free (no upkeep), full (8 units, weights only), small (2 units), drift (random
selection), five (hand-made organs: memory, spotlight, watcher, brake, skin; gates and parameters evolve, same upkeep per organ).
Fitness: mean fraction of life survived - cost per unit and edge - small cost of |u| and shield.  Evolution is
across generations, within-life weights are fixed: an agent here does not redesign itself while alive."""
import sys, os, json
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
K, NI, X, T = 8, 6, 6.0, 150
CU, CE = .01, .0015
NC = 6
LPC = 8
GENS, POP = 80, 80


def world(cls, rng, T, P, L, shift=False):
    # pre-drawn noise shared by the whole population
    return dict(n=rng.standard_normal((T, L)), z1=rng.standard_normal((T, L)) * 2, z2=rng.standard_normal((T, L)) * 2,
                flip=rng.random((T, L)) < .03, lie=rng.random((T, L)) < .15, lieval=rng.standard_normal((T, L)) * 4,
                burst=rng.random((T, L)) < .05, bsgn=rng.choice([-1., 1.], (T, L)), drift=rng.choice([-.15, .15], L),
                m0=rng.choice([-1., 1.], L), shift=shift, cls=cls)


def simulate(act, st0, W, P, L, T, abl=None):
    """act(st, obs) -> (u, g, st); obs (P,L,NI)."""
    c = W["cls"]; x = np.zeros((P, L)); alive = np.ones((P, L), bool); life = np.zeros((P, L)); eff = np.zeros((P, L))
    m = np.broadcast_to(W["m0"], (P, L)).copy(); up = np.zeros((P, L)); hist = [np.zeros((P, L))] * 3
    cum = np.zeros((P, L)); st = st0; late = np.zeros((P, L))
    for t in range(T):
        cue = np.zeros(L)
        m = np.where((c == 1) & W["flip"][t], -m, m); cue = np.where((c == 1) & (W["flip"][t] | (t == 0)), m[0], 0.)
        mm = np.where(c == 1, m, 1.)
        if W["shift"] and t >= T // 2: mm = -mm
        sn = np.where(c == 5, .3 + .01 * cum, .3)
        y = x + W["z1"][t] * np.where(c == 0, .5, 0.)
        y = np.where((c == 2) & W["lie"][t], W["lieval"][t], y)
        obs = np.stack([y, np.broadcast_to(W["z1"][t], (P, L)), np.broadcast_to(W["z2"][t], (P, L)), np.broadcast_to(cue, (P, L)), up, np.ones((P, L))], -1)
        if abl is not None: obs = abl(obs)
        u, g, st = act(st, obs); u = np.clip(u, -3, 3); hist = [u] + hist[:2]
        ue = np.where(c == 4, hist[2], u); up = u
        b = np.where(c == 3, W["burst"][t] * W["bsgn"][t] * 4. * (1 - g), 0.)
        x = 1.1 * x + mm * ue + W["drift"] + sn * W["n"][t] + b
        cum += np.abs(u) * alive; eff += (np.abs(u) * .01 + .02 * g) * alive
        alive = alive & (np.abs(x) <= X); life += alive
        x = np.where(alive, x, 0.)
        if t >= T // 2: late += alive
    return life / T, late / (T - T // 2), eff / T


def net_act(G):
    Wr, Wi, Wo = G["Wr"] * G["Er"], G["Wi"] * G["Ei"], G["Wo"]; A = G["A"][:, None, :]
    def f(h, o):
        h = np.tanh(np.einsum("plk,pkj->plj", h, Wr) + np.einsum("pli,pij->plj", o, Wi)) * A
        r = np.einsum("plk,pko->plo", h, Wo)
        return 3 * np.tanh(r[..., 0]), 1 / (1 + np.exp(-(r[..., 1] * 3 - 2))), h
    return f


def five_act(G):
    g = G["gate"][:, None, :]; p = G["par"][:, None, :]
    def f(st, o):
        mem, sgn, yh = st; y = o[..., 0] - np.where(g[..., 1], p[..., 1], 0.) * o[..., 1]
        sgn = np.where(g[..., 0] & (o[..., 3] != 0), np.sign(o[..., 3]), sgn)
        bad = g[..., 2] & (np.abs(y - yh) > np.abs(p[..., 2]) + .5); y = np.where(bad, yh, y)
        a = 1 / (1 + np.exp(-p[..., 3])); mem = np.where(g[..., 0], a * mem + (1 - a) * y, y)
        k = np.where(g[..., 3], p[..., 4], 1.2); u = -np.where(g[..., 0], sgn, 1.) * k * mem + p[..., 5]
        sh = np.where(g[..., 4] & (np.abs(y) > 10 * np.abs(p[..., 6]) * .1), 1., 0.) * 1 / (1 + np.exp(-p[..., 7]))
        yh = 1.1 * y + np.where(g[..., 0], sgn, 1.) * np.clip(u, -3, 3)
        return u, sh, (mem, sgn, yh)
    return f


def new(arm, P, rng):
    if arm == "five": return dict(gate=rng.random((P, 5)) < .5, par=rng.normal(0, .5, (P, 8)))
    n0 = {"small": 2, "full": K}.get(arm, 1); A = np.zeros((P, K)); A[:, :n0] = 1
    Er = rng.random((P, K, K)) < .4; Ei = rng.random((P, NI, K)) < .6
    if arm in ("full", "small"): Er[:] = True; Ei[:] = True
    return dict(Wr=rng.normal(0, .4, (P, K, K)), Wi=rng.normal(0, .4, (P, NI, K)), Wo=rng.normal(0, .5, (P, K, 2)), Er=Er, Ei=Ei, A=A)


def cost(arm, G):
    if arm == "free": return np.zeros(len(next(iter(G.values()))))
    if arm == "five": return CU * G["gate"].sum(1)
    on = G["A"]; e = (G["Er"] * on[:, :, None] * on[:, None, :]).sum((1, 2)) + (G["Ei"] * on[:, None, :]).sum((1, 2))
    return CU * on.sum(1) + CE * e


def mutate(arm, G, rng):
    P = len(next(iter(G.values()))); H = {k: v.copy() for k, v in G.items()}
    if arm == "five":
        H["gate"] ^= rng.random((P, 5)) < .05; H["par"] += rng.normal(0, .25, (P, 8)) * (rng.random((P, 8)) < .4); return H
    for k in ("Wr", "Wi", "Wo"): H[k] += rng.normal(0, .25, H[k].shape) * (rng.random(H[k].shape) < .2)
    if arm in ("emerge", "free", "drift"):
        for k in ("Er", "Ei"): H[k] ^= rng.random(H[k].shape) < .03
        H["A"] = np.where(rng.random((P, K)) < .03, 1 - H["A"], H["A"]); H["A"][H["A"].sum(1) == 0, 0] = 1
    return H


def evolve(arm, classes, seed, gens=None, P=None):
    gens = gens or GENS; P = P or POP
    rng = np.random.default_rng([seed, hash_(arm), len(classes), *classes]); cl = np.repeat(classes, LPC); L = len(cl)
    G = new(arm, P, rng); act = five_act if arm == "five" else net_act
    for g in range(gens):
        f, _, e = simulate(act(G), st0(arm, P, L), world(cl, rng, T, P, L), P, L, T)
        fit = f.mean(1) - cost(arm, G) - e.mean(1) if arm != "free" else f.mean(1) - e.mean(1)
        order = np.argsort(-fit) if arm != "drift" else rng.permutation(P)
        top = order[:P // 4]; par = np.concatenate([top[:2], rng.choice(top, P - 2)])
        child = {k: v[par] for k, v in G.items()}; m = mutate(arm, child, rng)
        for k in m: m[k][:2] = child[k][:2]
        G = m
    f, _, e = simulate(act(G), st0(arm, P, L), world(cl, rng, T, P, L), P, L, T)
    b = int(np.argmax(f.mean(1) - cost(arm, G) - e.mean(1)))
    return {k: v[b:b + 1] for k, v in G.items()}


def hash_(s): import zlib; return zlib.crc32(s.encode()) % 10000


def st0(arm, P, L):
    if arm == "five": z = np.zeros((P, L)); return (z, np.ones((P, L)), z)
    return np.zeros((P, L, K))


def measure(arm, G, classes, seed):
    rng = np.random.default_rng([seed, 999]); cl = np.repeat(classes, 40); L = len(cl); act = five_act if arm == "five" else net_act
    W = lambda sh=False: world(cl, np.random.default_rng([seed, 998]), T, 1, L, sh)
    go = lambda H, sh=False, ab=None: [float(v.mean()) for v in simulate(act(H), st0(arm, 1, L), W(sh), 1, L, T, ab)[:2]]
    out = dict(base=go(G)[0], shift=go(G, True)[1], base_late=go(G)[1], units=float(G["A"].sum()) if arm != "five" else float(G["gate"].sum()), cost=float(cost(arm, G)[0]))
    base = out["base"]
    # generalisation: the same genome in a fresh world containing all six classes (40 lives each)
    clg = np.repeat(tuple(range(NC)), 40); Lg = len(clg)
    lg = simulate(act(G), st0(arm, 1, Lg), world(clg, np.random.default_rng([seed, 997]), T, 1, Lg), 1, Lg, T)[0].reshape(NC, 40).mean(1)
    out["gen_by_class"] = [round(float(v), 4) for v in lg]; out["gen"] = float(lg.mean())
    own = set(classes); out["gen_other"] = float(np.mean([lg[i] for i in range(NC) if i not in own])) if len(own) < NC else out["gen"]
    if arm == "five":
        for i, nm in enumerate(("memory", "spotlight", "watcher", "brake", "skin")):
            H = {k: v.copy() for k, v in G.items()}; H["gate"][:, i] = False; out["abl_" + nm] = base - go(H)[0]
        out["gates"] = [int(v) for v in G["gate"][0]]; return out
    H = {k: v.copy() for k, v in G.items()}; H["Er"][:] = False; out["abl_recurrence"] = base - go(H)[0]
    for nm, i in (("y", 0), ("z1", 1), ("z2", 2), ("cue", 3), ("uprev", 4)):
        def ab(o, i=i): o = o.copy(); o[..., i] = 0.; return o
        out["abl_" + nm] = base - go(G, False, ab)[0]
    H = {k: v.copy() for k, v in G.items()}; H["Wo"][..., 1] = -5.; out["abl_skin"] = base - go(H)[0]
    return out


ARMS = ("emerge", "free", "full", "small", "drift", "five")
SETS = {"mix": tuple(range(NC)), **{f"c{i}": (i,) for i in range(NC)}}


def run(seed, sets=SETS, arms=ARMS):
    out = {}
    for s, cls in sets.items():
        out[s] = {}
        for a in arms:
            G = evolve(a, cls, seed); out[s][a] = measure(a, G, cls, seed)
            print(seed, s, a, {k: (round(v, 3) if isinstance(v, float) else v) for k, v in out[s][a].items()}, flush=True)
    return out


if __name__ == "__main__":
    if sys.argv[1] in ("dev", "confirm"):
        sets = SETS if len(sys.argv) < 4 else {sys.argv[3]: SETS[sys.argv[3]]}
        if len(sys.argv) > 5: GENS, POP = int(sys.argv[4]), int(sys.argv[5])
        tag = "" if len(sys.argv) < 4 else f"_{sys.argv[3]}_g{GENS}"
        json.dump(run(int(sys.argv[2]), sets), open(os.path.join(HERE, f"{sys.argv[1]}_{sys.argv[2]}{tag}.json"), "w"), indent=1)
