"""Score the emergence confirm. Usage: python emerge_score.py dev|confirm SEED... -> score_{mode}.json
Reads {mode}_{seed}_{set}_g400.json for the 7 sets. Rules: PREREG_emergence_2026-11-26.md."""
import sys, os, json, statistics as st
HERE = os.path.dirname(os.path.abspath(__file__))
SETS = ["mix", "c0", "c1", "c2", "c3", "c4", "c5"]
NETS = ["emerge", "free", "full", "small"]
mode, seeds = sys.argv[1], [int(s) for s in sys.argv[2:]]
D = {s: {k: json.load(open(os.path.join(HERE, f"{mode}_{s}_{k}_g400.json")))[k] for k in SETS} for s in seeds}
n = len(seeds); need = n - 1 if n >= 4 else n   # "4 of 5"
R = {}
def put(k, ok, det): R[k] = dict(pass_=bool(ok), detail=det)

c = [D[s]["mix"]["five"]["base"] - max(D[s]["mix"][a]["base"] for a in NETS) for s in seeds]
put("E1", sum(v >= .05 for v in c) >= need, c)
c = [(D[s]["mix"]["emerge"]["gen_by_class"][1], D[s]["mix"]["five"]["gen_by_class"][1]) for s in seeds]
put("E2", sum(e <= .35 and f >= .9 for e, f in c) >= need, c)
f1 = [D[s]["c1"]["five"]["base"] for s in seeds]; e1 = [D[s]["c1"]["emerge"]["base"] for s in seeds]
put("E3", all(v >= .95 for v in f1) and st.median(e1) <= .9, dict(five=f1, emerge=e1, median=st.median(e1)))
cells = [(s, a, D[s]["c1"][a]["abl_cue"]) for s in seeds for a in ("emerge", "free") if D[s]["c1"][a]["base"] >= .8]
put("E4", len(cells) > 0 and all(v >= .25 for _, _, v in cells), dict(cells=cells, evaluable=len(cells) > 0))
m = [(D[s]["c1"]["five"]["gates"][0], D[s]["c1"]["five"]["abl_memory"]) for s in seeds]
b = [(D[s]["c4"]["five"]["gates"][3], D[s]["c4"]["five"]["abl_brake"]) for s in seeds]
put("E5", sum(g == 1 and v >= .5 for g, v in m) >= need and sum(g == 1 and v >= .5 for g, v in b) >= need, dict(c1_memory=m, c4_brake=b))
w = [(D[s]["c2"]["five"]["gates"][2], D[s]["c2"]["five"]["abl_watcher"]) for s in seeds]
k = [D[s]["c3"]["five"]["abl_skin"] for s in seeds]
put("E6", sum(g == 0 or v < .05 for g, v in w) >= need and sum(v < .05 for v in k) >= need, dict(c2_watcher=w, c3_skin=k))
cl = [(s, c_, D[s][c_]["emerge"]["base"] - D[s][c_]["full"]["base"], D[s][c_]["emerge"]["units"]) for s in seeds for c_ in ("c0", "c2", "c3", "c4", "c5")]
ok = sum(d >= -.05 and u <= 2 for _, _, d, u in cl)
put("E7", ok >= len(cl) - (3 if n == 5 else max(0, round(.12 * len(cl)))), dict(ok=ok, of=len(cl), cells=cl))
c = [all(D[s][k_]["drift"]["base"] < D[s][k_]["emerge"]["base"] for k_ in SETS) for s in seeds]
put("E8", sum(c) >= need, c)
ue = st.mean(D[s][k_]["emerge"]["units"] for s in seeds for k_ in SETS); uf = st.mean(D[s][k_]["free"]["units"] for s in seeds for k_ in SETS)
put("E9", ue < uf, dict(emerge=ue, free=uf))
med = [st.median(D[s][k_][a]["shift"] for k_ in SETS for a in NETS + ["drift", "five"]) for s in seeds]
fs = max(D[s][k_]["five"]["shift"] for s in seeds for k_ in SETS)
put("E10", all(v <= .15 for v in med) and fs <= .15, dict(median_shift=med, max_five_shift=fs))
g1 = [(st.mean(D[s][f"c{i}"]["emerge"]["gen"] for i in range(6)), D[s]["mix"]["emerge"]["gen"]) for s in seeds]
g2 = [(D[s]["mix"]["five"]["gen"], max(D[s]["mix"][a]["gen"] for a in NETS)) for s in seeds]
put("E11", sum(a < b_ for a, b_ in g1) >= need and sum(a >= b_ + .05 for a, b_ in g2) >= need, dict(specialist_vs_mix=g1, five_vs_nets=g2))
v = [D[s][f"c{i}"][a]["gen_by_class"][1] for s in seeds for i in (0, 2, 3, 4, 5) for a in NETS]
put("E12", sum(x <= .35 for x in v) >= .95 * len(v), dict(ok=sum(x <= .35 for x in v), of=len(v)))
out = dict(mode=mode, seeds=seeds, passed=sum(r["pass_"] for r in R.values()), of=len(R), results=R)
json.dump(out, open(os.path.join(HERE, f"score_{mode}.json"), "w"), indent=1)
for k_, r in R.items(): print(k_, "PASS" if r["pass_"] else "FAIL", json.dumps(r["detail"])[:200])
print(f"{out['passed']} of {out['of']}")
