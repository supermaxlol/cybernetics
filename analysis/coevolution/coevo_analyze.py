"""Scores the co-evolution hypotheses C1–C10 (PREREG_coevolution_2026-11-23.md).
Usage: python coevo_analyze.py dev|confirm
"""
import sys, os, json
from collections import defaultdict
import numpy as np
from scipy import stats
HERE = os.path.dirname(os.path.abspath(__file__))


def boundary(cells):
    """Largest drift ratio with survival >= 0.5, or 0 if none."""
    ok = [c["ratio"] for c in cells if c["surv"] >= 0.5]
    return max(ok) if ok else 0.0


def analyze(mode):
    D = json.load(open(os.path.join(HERE, f"coevo_{mode}_raw.json"))); R = {}
    e1 = D["e1"]
    # C1: noiseless clip policy matches the Lean rate_iff threshold exactly
    z = [c for c in e1 if c["s"] == 0 and c["policy"] == "clip"]
    R["C1_mismatch"] = sum((c["surv"] == 1.0) != (c["ratio"] <= 1.0 + 1e-9) for c in z)
    R["C1_pass"] = R["C1_mismatch"] == 0
    G = defaultdict(list)
    for c in e1: G[(c["X"], c["eta"], c["r"], c["policy"], c["s"])].append(c)
    bd = {k: boundary(v) for k, v in G.items()}
    R["C2_boundaries"] = {str(k): v for k, v in bd.items()}
    # C2: noise moves the boundary down; it is below the noiseless threshold for s >= 0.15
    fams = sorted({k[:4] for k in bd})
    mono = all(all(bd[f + (s1,)] >= bd[f + (s2,)] for s1, s2 in ((0.0, 0.05), (0.05, 0.15), (0.15, 0.3))) for f in fams)
    below = all(bd[f + (s,)] < 1.0 for f in fams for s in (0.15, 0.3))
    R["C2_pass"] = mono and below
    # C3: shaping the niche raises the tolerable absolute drift v* = boundary·(r + ηX) at s = 0.3
    vs = {}
    for (X, eta, r, pol, s), b in bd.items():
        if s == 0.3: vs[(X, r, pol, eta)] = b * (r + eta * X)
    c3 = []
    for X, r, pol in sorted({(k[0], k[1], k[2]) for k in vs}):
        seq = [vs[(X, r, pol, eta)] for eta in (0.0, 0.05, 0.15)]
        c3.append(dict(X=X, r=r, policy=pol, vstar=seq, ok=seq[0] <= seq[1] <= seq[2] and seq[2] > seq[0]))
    R["C3"] = c3; R["C3_pass"] = all(c["ok"] for c in c3)
    # C4: depletion
    e2 = D["e2"]
    R["C4_beta_pos_survivors"] = sum(c["surv"] > 0 for c in e2 if c["beta"] > 0)
    rat = [c["ttd"] / c["tstar"] for c in e2 if c["beta"] > 0 and c["sq"] > 0]
    R["C4_ttd_ratio_range"] = [min(rat), max(rat)]
    R["C4_exo_surv_min"] = min(c["surv"] for c in e2 if c["beta"] == 0 and c["mu"] > 0)
    R["C4_static_viable_dead"] = sum(c["static_viable"] and c["surv"] == 0 for c in e2 if c["beta"] > 0)
    R["C4_pass"] = R["C4_beta_pos_survivors"] == 0 and all(abs(x - 1) <= 0.05 for x in rat) and R["C4_exo_surv_min"] >= 0.95
    # C5: interior optimum of capacity investment; over-investment dies of budget, under-investment of drift
    e3 = D["e3"]; c5 = []
    for a in sorted({c["a"] for c in e3}):
        for s in sorted({c["s"] for c in e3}):
            cc = sorted([c for c in e3 if c["a"] == a and c["s"] == s], key=lambda c: c["b"])
            bs = [c["b"] for c in cc]; tt = [c["ttd"] for c in cc]
            i = int(np.argmax(tt))
            c5.append(dict(a=a, s=s, b=bs, ttd=tt, argmax_b=bs[i], interior=0 < i < len(bs) - 1,
                           low_b_drift=cc[0]["frac_budget"] == 0.0, high_b_budget=cc[-1]["frac_budget"] == 1.0))
    R["C5"] = c5
    R["C5_pass"] = all(c["interior"] and c["low_b_drift"] and c["high_b_budget"] for c in c5)
    R["C5b_all_die"] = all(c["ttd"] < 20000 for c in e3)            # Lean accel_impossible: everyone dies
    # C6: deterministic recursion predicts noisy mean ttd (s = 0.05) within 10%
    r6 = [c["ttd"] / c["ttd_det"] for c in e3 if c["s"] == 0.05]
    R["C6_ratio_range"] = [min(r6), max(r6)]; R["C6_pass"] = all(abs(x - 1) <= 0.10 for x in r6)
    # C7–C10 ultrastability
    e4 = D["e4"]
    m1 = [c for c in e4 if c["md"] == 1]
    R["C7_min_ultra"] = min(c["ultra"]["surv"] for c in m1)
    marg = [c["ultra"]["surv"] - max(c["brake"]["surv"], c["nobrake"]["surv"]) for c in m1]
    R["C7_margin_min_mean"] = [min(marg), float(np.mean(marg))]
    R["C7_pass"] = min(marg) > 0 and np.mean(marg) >= 0.3
    md5 = {(c["lam"], c["tau"]): c["ultra"]["surv"] for c in e4 if c["md"] == 5}
    d8 = [md5[(c["lam"], c["tau"])] - c["ultra"]["surv"] for c in m1]
    R["C8_mean_md5_minus_md1"] = float(np.mean(d8)); R["C8_pass"] = R["C8_mean_md5_minus_md1"] < -0.1
    R["C9_pass"] = all(c["oracle"]["surv"] >= c["ultra"]["surv"] for c in e4)
    rho, p = stats.spearmanr([c["tau"] for c in m1], [c["ultra"]["switches"] for c in m1])
    R["C10_spearman_tau_switches"] = [float(rho), float(p)]; R["C10_pass"] = rho < 0 and p < 0.05
    json.dump(R, open(os.path.join(HERE, f"coevo_{mode}_results.json"), "w"), indent=1, default=str)
    for k in sorted(R):
        if k.endswith("pass") or k.endswith("die"): print(k, R[k])
    return R


if __name__ == "__main__":
    analyze(sys.argv[1] if len(sys.argv) > 1 else "dev")
