"""Hypothesis tests for the stochastic programme. Usage: python analyze.py dev|confirm
Reads stoch_<mode>_raw.json and writes stoch_<mode>_results.json. Every test is listed in
PREREG_stochastic_2026-11-23.md. CIs are 95% percentile bootstraps over environments (2000 resamples).
"""
import sys, json, math, os
import numpy as np
from scipy import stats
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from stoch_sim import f_res

HERE = os.path.dirname(os.path.abspath(__file__))
ORG = "SMPBW"
import itertools
CFGS = list(itertools.product([0, 1], repeat=5))
IDX = {c: i for i, c in enumerate(CFGS)}
RNG = np.random.default_rng(0)


def boot(v, f=np.mean, B=2000):
    v = np.asarray(v, float); v = v[~np.isnan(v)]
    if len(v) < 3: return [float("nan")] * 3
    bs = [f(v[RNG.integers(0, len(v), len(v))]) for _ in range(B)]
    return [float(f(v)), float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))]


def marg(row, j, where=None):
    """Mean survival gain from adding organ j, over the 16 pairs (optionally restricted)."""
    s = row["surv"]; out = []
    for c in CFGS:
        if c[j] == 0: continue
        c0 = c[:j] + (0,) + c[j + 1:]
        if where is None or where(c): out.append(s[IDX[c]] - s[IDX[c0]])
    return float(np.mean(out))


def inter(row, i, j, where=lambda c: True):
    """Interaction surv(i,j) − surv(i) − surv(j) + surv(neither), averaged over the other organs."""
    s = row["surv"]; out = []
    for c in CFGS:
        if c[i] or c[j] or not where(c): continue
        def w(a, b):
            d = list(c); d[i] = a; d[j] = b; return s[IDX[tuple(d)]]
        out.append(w(1, 1) - w(1, 0) - w(0, 1) + w(0, 0))
    return float(np.mean(out))


def analyze(mode):
    raw = json.load(open(os.path.join(HERE, f"stoch_{mode}_raw.json")))
    A = raw["atlas"]; R = {}
    E = lambda k: np.array([r["env"][k] for r in A])
    delay, g, lam, qm, K, a_s = E("delay"), E("g"), E("lam"), E("q_miss"), E("K"), E("a_s")
    B = ORG.index("B"); M = ORG.index("M"); W = ORG.index("W"); S = ORG.index("S"); P = ORG.index("P")
    mB = np.array([marg(r, B) for r in A])
    # H1 Brake sign flip
    R["H1_brake_delay_g>=1"] = boot(mB[delay & (g >= 1)])
    R["H1_brake_nodelay"] = boot(mB[~delay])
    R["H1_pass"] = R["H1_brake_delay_g>=1"][1] > 0 and R["H1_brake_nodelay"][2] < 0
    # H2 Brake value under delay rises with feedback strength g (phase boundary near g = 1)
    rho, p = stats.spearmanr(g[delay], mB[delay]); R["H2_spearman_g_brake_delay"] = [float(rho), float(p)]
    R["H2_pass"] = rho > 0 and p < 0.01
    bins = [0.7, 0.8, 0.9, 1.0, 1.1, 1.21]
    R["phase_brake_by_g"] = {f"delay={int(d)},g=[{lo},{hi})": boot(mB[(delay == d) & (g >= lo) & (g < hi)])
                             for d in (0, 1) for lo, hi in zip(bins[:-1], bins[1:])}
    # H3 worst-case necessity vs average-case necessity (2x2 per organ x env)
    cls = [r["cls"]["1.0"] for r in A]
    tab = {o: {"wc&avg": 0, "wc&~avg": 0, "~wc&avg": 0, "~wc&~avg": 0, "prac": 0, "avg&~prac": 0} for o in ORG}
    for c in cls:
        for o in ORG:
            w, a = c[o]["wc"], c[o]["avg"]
            tab[o][("wc" if w else "~wc") + "&" + ("avg" if a else "~avg")] += 1
            tab[o]["prac"] += c[o]["prac"]; tab[o]["avg&~prac"] += a and not c[o]["prac"]
    R["H3_table"] = tab
    nwc = sum(t["wc&avg"] + t["wc&~avg"] for t in tab.values())
    R["H3_frac_wc_not_avg"] = sum(t["wc&~avg"] for t in tab.values()) / max(nwc, 1)
    R["H3_n_avg_not_wc"] = sum(t["~wc&avg"] for t in tab.values())
    R["H3_pass"] = R["H3_frac_wc_not_avg"] >= 0.2 and R["H3_n_avg_not_wc"] > 0
    R["n_envs_any_wc_viable"] = int(sum(any(r["wc"]) for r in A))
    # practical vs average sensitivity to the cost conversion rate
    R["practical_by_rho"] = {rc: {o: float(np.mean([r["cls"][rc][o]["prac"] for r in A])) for o in ORG}
                             for rc in ("0.5", "1.0", "2.0")}
    R["average_rate"] = {o: float(np.mean([c[o]["avg"] for c in cls])) for o in ORG}
    R["worst_rate"] = {o: float(np.mean([c[o]["wc"] for c in cls])) for o in ORG}
    # H6 Memory without Watcher under shifts: harm shrinks as slow-memory rate a_s grows
    mM_noW = np.array([marg(r, M, where=lambda c: c[W] == 0) for r in A])
    sh = lam > 0
    R["H6_M_noW_shift_frozen"] = boot(mM_noW[sh & (a_s == 0)])
    R["H6_M_noW_shift_ema"] = boot(mM_noW[sh & (a_s > 0)])
    rho6, p6 = stats.spearmanr(a_s[sh & (a_s > 0)], mM_noW[sh & (a_s > 0)])
    R["H6_spearman_as"] = [float(rho6), float(p6)]
    iMW = np.array([inter(r, M, W) for r in A])
    R["H6_MW_interaction_shift"] = boot(iMW[sh])
    R["H6_pass"] = R["H6_M_noW_shift_frozen"][2] < 0 and R["H6_MW_interaction_shift"][1] > 0 and \
        R["H6_M_noW_shift_ema"][0] > R["H6_M_noW_shift_frozen"][0]
    # H7 imperfect monitoring: Watcher value falls with miss probability (given M, under shifts)
    mW_M = np.array([marg(r, W, where=lambda c: c[M] == 1) for r in A])
    rho7, p7 = stats.spearmanr(qm[sh], mW_M[sh]); R["H7_spearman_qmiss"] = [float(rho7), float(p7)]
    R["H7_pass"] = rho7 < 0 and p7 < 0.05
    R["phase_watcher_by_K"] = {f"K={lo}-{hi}": boot(mW_M[sh & (K >= lo) & (K <= hi)]) for lo, hi in ((1, 3), (4, 6), (7, 9), (10, 12))}
    # H8 Skin x Spotlight: substitutes (negative interaction); less so at long latency K
    iSP = np.array([inter(r, S, P) for r in A])
    R["H8_SP_interaction"] = boot(iSP)
    rho8, p8 = stats.spearmanr(K[sh], iSP[sh]); R["H8_spearman_K"] = [float(rho8), float(p8)]
    R["H8_pass"] = R["H8_SP_interaction"][2] < 0 and rho8 > 0 and p8 < 0.05
    R["phase_SP_by_K"] = {f"K={lo}-{hi}": boot(iSP[(K >= lo) & (K <= hi)]) for lo, hi in ((1, 3), (4, 6), (7, 9), (10, 12))}
    # H12 resource priority: under delay with scarce income, funding the Brake first beats funding Watcher/Memory first
    full = IDX[(1, 1, 1, 1, 1)]
    prio = E("prio"); inc = E("income"); cost = np.array([sum(r["env"]["cost"]) for r in A])
    scarce = delay & (cost > inc) & (g >= 1)
    mean_all = np.array([np.mean(r["surv"]) for r in A])
    R["H12_n"] = [int((scarce & (prio == "BSPWM")).sum()), int((scarce & (prio == "WMPSB")).sum())]
    R["H12_mean_surv_Bfirst"] = boot(mean_all[scarce & (prio == "BSPWM")])
    R["H12_mean_surv_Wfirst"] = boot(mean_all[scarce & (prio == "WMPSB")])
    R["H12_pass"] = R["H12_mean_surv_Bfirst"][0] - R["H12_mean_surv_Wfirst"][0] > 0.05
    # failure response (mid-run, full config)
    resp = {}
    for o in ORG:
        d = [r["fail"][o]["surv"] - r["fail"][o]["surv_ctrl"] for r in A if r["fail"][o]["surv"] is not None]
        dd = [r["fail"][o]["surv"] - r["fail"][o]["surv_ctrl"] for r, de, gg in zip(A, delay, g)
              if r["fail"][o]["surv"] is not None and de and gg >= 1]
        ta = [r["fail"][o]["ttd_after"] for r in A if r["fail"][o]["ttd_after"] is not None]
        resp[o] = dict(drop_all=boot(d), drop_delay_g1=boot(dd), median_ttd_after=float(np.median(ta)) if ta else None)
    R["failure_response"] = resp
    # cost of viability: cheapest config reaching 0.9 survival, by environment class
    def cheapest(r):
        cs = [(sum(r["env"]["cost"][i] for i in range(5) if c[i]), c) for c in CFGS if r["surv"][IDX[c]] >= 0.9]
        return min(cs)[1] if cs else None
    ch = [cheapest(r) for r in A]
    R["cheapest_viable_rate"] = float(np.mean([c is not None for c in ch]))
    R["cheapest_contains"] = {cls_: {o: float(np.mean([c[j] for c, de in zip(ch, delay) if c is not None and de == d]))
                                     for j, o in enumerate(ORG)} for cls_, d in (("delay", True), ("nodelay", False))}
    # H4 diffusion scaling
    sc = raw["scaling"]
    gi = [c for c in sc if c["rho"] == 0 and c["dist"] == "gauss"]
    x = np.log([c["X"] ** 2 / c["a"] ** 2 for c in gi]); y = np.log([c["mean_ttd"] for c in gi])
    sl = stats.linregress(x, y)
    R["H4_slope_gauss"] = [float(sl.slope), float(sl.stderr)]
    C = float(np.mean([c["mean_ttd"] * c["a"] ** 2 / c["X"] ** 2 for c in gi]))
    R["H4_constant"] = C
    preds = []
    for c in sc:
        pr = CONST * c["X"] ** 2 / (c["a"] ** 2 * f_res(c["rho"]))
        preds.append(dict(X=c["X"], a=c["a"], rho=c["rho"], dist=c["dist"], obs=c["mean_ttd"], pred=pr,
                          ratio=c["mean_ttd"] / pr, censored=c["censored"]))
    R["H4_predictions"] = preds
    R["H4_pass_slope"] = abs(sl.slope - 1) <= 0.15
    R["H4b_pass_ratio"] = all(0.75 <= p["ratio"] <= 1.25 for p in preds)
    R["H4c_rho_direction"] = None
    rr = {}
    for p in preds:
        rr.setdefault((p["X"], p["a"]), {})[(p["rho"], p["dist"])] = p["obs"]
    dirs = [v[(0.8, "gauss")] > v[(0.0, "gauss")] for v in rr.values() if (0.8, "gauss") in v]
    R["H4c_persistent_slower"] = bool(dirs) and all(dirs)
    # H5 Chebyshev
    ch5 = raw["cheb"]
    R["H5"] = ch5
    iid = [cc for c in ch5 if c["rho"] == 0 for cc in c["cells"]]
    R["H5_iid_violations"] = sum(cc["freq"] > cc["bound"] + 3 * math.sqrt(cc["bound"] * (1 - cc["bound"]) / 4000 + 1e-12) for cc in iid)
    ar = [cc for c in ch5 if c["rho"] == 0.8 for cc in c["cells"]]
    R["H5_ar08_violations"] = sum(cc["freq"] > cc["bound"] for cc in ar)
    R["H5_var_check"] = [(c["brake"], c["rho"], c["var_emp"], c["var_theory_iid"]) for c in ch5]
    R["H5_pass"] = R["H5_iid_violations"] == 0 and R["H5_ar08_violations"] >= 1
    # H9 resource competition (control arm): alive fraction tracks min(1, ratio)
    pop = raw["pop"]
    ctrl = [(p["ratio"], p["control"]["alive_frac"]) for p in pop if p["chi"] <= 0.5]
    R["H9_cells"] = ctrl
    R["H9_pass"] = all(a <= r + 0.05 for r, a in ctrl if r < 1) and all(a >= 0.9 for r, a in ctrl if r >= 1.5)
    # H10 propagation (zombie mode: failed units stay coupled, as in CoupledPartial)
    def pv(cond, arm, key):
        v = [p[arm][key] for p in pop if cond(p) and p[arm][key] is not None]
        return float(np.mean(v)) if v else None
    Z = lambda chi: (lambda p: p["zombie"] and p["ratio"] >= 1.0 and p["chi"] == chi)
    R["H10_table"] = {str(chi): dict(others_dead_ctrl=pv(Z(chi), "control", "others_dead_frac"),
                                     others_dead_one=pv(Z(chi), "one_unbraked", "others_dead_frac"),
                                     u0_dead=pv(Z(chi), "one_unbraked", "u0_dead"),
                                     agg_surv_one=pv(Z(chi), "one_unbraked", "agg_surv"),
                                     agg_surv_ctrl=pv(Z(chi), "control", "agg_surv"))
                      for chi in (0.0, 0.2, 0.5, 0.8)}
    ex = [p["one_unbraked"]["others_dead_frac"] - p["control"]["others_dead_frac"] for p in pop
          if p["zombie"] and p["ratio"] >= 1.0]
    chis = [p["chi"] for p in pop if p["zombie"] and p["ratio"] >= 1.0]
    rho10, p10 = stats.spearmanr(chis, ex) if np.std(ex) > 0 else (float("nan"), float("nan"))
    R["H10a_spearman_chi_excess"] = [float(rho10), float(p10)]
    R["H10a_pass"] = bool(rho10 > 0 and p10 < 0.05)
    t = R["H10_table"]
    R["H10b_pass"] = t["0.5"]["u0_dead"] <= 0.2 and t["0.0"]["u0_dead"] >= 0.8
    R["H10c_pass"] = t["0.8"]["others_dead_ctrl"] >= 0.5 and t["0.0"]["others_dead_ctrl"] <= 0.02 and \
        t["0.2"]["others_dead_ctrl"] <= 0.02
    # H11 failure response: after the Brake fails (delay, g >= 1) the loop has roots with |z|^2 = g, so
    # time-to-failure falls as g rises (exponential escape for g > 1, diffusive escape at g = 1)
    sel = [(r["env"]["g"], r["fail"]["B"]["ttd_after"]) for r in A
           if r["env"]["delay"] and r["env"]["g"] >= 1.0 and r["fail"]["B"]["ttd_after"] is not None]
    rho11, p11 = stats.spearmanr([a for a, b in sel], [b for a, b in sel]) if len(sel) >= 5 else (float("nan"),) * 2
    R["H11_n"] = len(sel); R["H11_spearman_g"] = [float(rho11), float(p11)]
    R["H11_pass"] = bool(rho11 < 0 and p11 < 0.05)
    out = os.path.join(HERE, f"stoch_{mode}_results.json")
    json.dump(R, open(out, "w"), indent=1, default=str)
    keys = [k for k in R if k.endswith("pass") or k.startswith("H") and not isinstance(R[k], (list, dict))]
    for k in sorted(R):
        if k.endswith("pass"): print(k, R[k])
    return R


CONST = 1.0      # H4 constant: dev estimate 0.998 (gaussian iid grid), fixed before confirm

if __name__ == "__main__":
    sys.path.insert(0, HERE)
    analyze(sys.argv[1] if len(sys.argv) > 1 else "dev")
