"""Score sense.py output. Usage: python sense_score.py dev|confirm SEED [SEED ...]. Pools seeds by the mean of each quantity."""
import sys, json
import numpy as np, sense as S
import glob
def load(seed):
    o = dict(s1={}, s2={}, s3={})
    for f in sorted(glob.glob(f"{sys.argv[1]}_{seed}_*.json")):
        d = json.load(open(f))
        for k in ("s1", "s2", "s3"): o[k].update(d[k])
        if "s4" in d: o["s4"] = d["s4"]
    return o
O = [load(s) for s in sys.argv[2:]]; n = len(O); C = list(O[0]["s1"]); out = {}
mean = lambda f: float(np.mean([f(o) for o in O]))
ci = lambda f: [round(float(v), 4) for v in (np.mean([f(o) for o in O]), np.min([f(o) for o in O]), np.max([f(o) for o in O]))]
def put(k, ok, **kw): out[k] = dict(passed=bool(ok), **kw); print(k, "PASS" if ok else "FAIL", json.dumps(kw))
arms = lambda o, c, M: [k for k in o["s1"][c][M]]
below = [(c, M, k, r["inv"]) for o in O for c in C for M, t in o["s1"][c].items() if int(M) < S.MSTAR[c] for k, r in t.items()]
at = [o["s1"][c][str(S.MSTAR[c])]["theory"]["inv"] for o in O for c in C]
put("P1", max(b[3] for b in below) == 0 and min(at) > .999, max_below=max(b[3] for b in below), min_uniform_at_Mstar=min(at))
need = {c: [next((int(M) for M in sorted(o["s1"][c], key=int) if o["s1"][c][M]["learn"]["inv"] > 0), None) for o in O] for c in C}
put("P2", all(m is not None and S.MSTAR[c] <= m <= S.MSTAR[c] + 1 for c in C for m in need[c]), first_M_nonempty=need, Mstar=S.MSTAR)
p3 = {c: ci(lambda o: o["s1"][c][str(S.MSTAR[c] - 1)]["learn"]["uni"]) for c in C if str(S.MSTAR[c] - 1) in O[0]["s1"][c]}
put("P3", sum(v[0] > .05 for v in p3.values()) >= 2, survival_at_Mstar_minus_1=p3)
ks = sorted(O[0]["s2"][C[0]], key=float); xs = [float(k) for k in ks]
low = [o["s2"][c][k]["linear"] for o in O for c in C for k in ks if float(k) <= 1]
dev = [abs(mean(lambda o: o["s2"][c][k]["linear"]) - O[0]["s2"][c][k]["closed"]) for c in C for k in ks if float(k) > 1]
put("P4", min(low) == 1 and max(dev) < .03, min_survival_at_or_below_sc=min(low), max_abs_dev_above=max(dev))
h50 = lambda o, c, a: S.s50(xs, [o["s2"][c][k][a] for k in ks])
r5 = {c: ci(lambda o: h50(o, c, "learn") / h50(o, c, "linear")) for c in C}
put("P5", all(abs(v[0] - 1) <= .10 for v in r5.values()), ratio=r5)
r6 = {c: ci(lambda o: h50(o, c, "mem") / h50(o, c, "linear")) for c in C}
put("P6", all(v[0] >= 1.15 for v in r6.values()), ratio=r6)
es = sorted(O[0]["s3"][C[0]], key=float); haz = lambda p: -np.log(np.clip(p, 1 / 8000, 1)) / S.T
d7 = max(abs(mean(lambda o: o["s3"][c][e]["linear"]) - O[0]["s3"][c][e]["operator"]) for c in C for e in es)
def slope(c, a):
    e = [k for k in es if float(k) > 0]; y = [haz(mean(lambda o: o["s3"][c][k][a])) for k in e]
    z = [(np.log(float(k)), np.log(v)) for k, v in zip(e, y) if v > 1e-7 and 1e-3 < np.exp(-v * S.T) < .9995]
    return float(np.polyfit(*zip(*z), 1)[0]) if len(z) >= 3 else None
s7 = {c: slope(c, "linear") for c in C}
put("P7", d7 < .03 and all(v is not None and .85 <= v <= 1.15 for v in s7.values()), max_abs_dev=d7, slope_linear=s7)
s8 = {c: slope(c, "mem") for c in C}; s8l = {c: slope(c, "learn") for c in C}
put("P8", all(v is not None and v >= 1.5 for v in s8.values()), slope_mem=s8, slope_learn=s8l)
ss = sorted(O[0]["s4"], key=float); sx = [float(k) for k in ss]
s50e = {a: ci(lambda o: S.s50(sx, [o["s4"][k][a] for k in ss])) for a in ("full", "five")}
sc4 = (6.0 - .15 - .3) / 1.1   # drift bound |drift| + one noise sd, radius 6, growth 1.1
put("P9", all(abs(v[0] / sc4 - 1) > .25 for v in s50e.values()), s50=s50e, s_c_drift=sc4)
print("passed", sum(v["passed"] for v in out.values()), "of", len(out), "seeds", n)
json.dump(out, open("score.json", "w"), indent=1)
