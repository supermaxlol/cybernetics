# Pre-registration, sensor scrambling confirm (frozen 2026-11-26, local clock only)

**Predictions.** P1-P9 are as written in `PREDICTIONS_before_dev_2026-11-26.md` (frozen, sha256 in PREDICTIONS.sha256) before any dev survival output was seen.
**Scoring.** `sense_score.py`, frozen here, was written before the dev results were seen (see DEVLOG). P9's numeric rule (|s_50 / s_c,drift - 1| > .25
for both arms, s_c,drift = (6 - .15 - .3)/1.1) was added there, because the predictions file gives a direction only.
**Code.** `sense.py`, frozen here. Confirm seeds: 7001, 7002, 7003, each run as five parts (A, B, C, D, 4). The score pools seeds by the mean.

**Dev result (seed 700), which the confirm is not blind to:** 5 of 9 passed. P3, P5, P6 and P8 failed. So the confirm can replicate or overturn
these failures but is no longer a blind test of them. P1, P2, P4, P7 and P9 are as risky as before (P1, P4, P7 are close to code checks).

**Post-dev expectations (labelled post-dev, NOT scored, so they cannot be counted as predictive successes):**
- Q1. Cell B: learned rules, with or without memory, have s_50 at least 15% above the linear rule; in A, C, D within 5%.
- Q2. The S3 hazard slope is about 1 (0.85-1.15) for all arms in all cells.
- Q3. S1 learned memory tables in C and D fail to reach any invariant set even at M* (search failure, not a bound).

**Limits.** All of this is a scalar linear world with bounded or replaced readings; the "learned" arms are one evolutionary search each.
The theorem's threshold is about worst-case survival; survival under random noise is an average-case question and is answered by
the closed forms, not by the counting bound.
