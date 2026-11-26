# Results, sensor scrambling confirm (seeds 7001-7003; 2026-11-26)

Frozen files verified by hash before scoring (FROZEN_sensing.sha256, PREDICTIONS.sha256). Score: `sense_score.py confirm 7001 7002 7003` -> score_confirm.json.
**4 of 9 passed.** Dev (seed 700) had 5 of 9; the confirm was not blind to P3, P5, P6, P8 (see PREREG).

| | Prediction | Confirm | Numbers (mean [min, max] over seeds) |
|---|---|---|---|
| P1 | no invariant set below M*; uniform table fully invariant at M* | PASS | max below 0; uniform at M* 1.0, all cells |
| P2 | learned memoryless tables first reach an invariant set at M* or M*+1 | **FAIL** | A, B, C exactly at M* in every seed; D: 8, 7, 6 (M* = 6). One seed needed M*+2 |
| P3 | learned tables at M*-1 survive > .05 under uniform noise in >= 2 cells | **FAIL** | A .0002, B 0, C 0, D .058 [0, .112]: one cell only |
| P4 | linear rule: survival 1 for s <= s_c, closed form above | PASS | min 1.0 at or below s_c; max deviation .008 |
| P5 | learned memoryless s_50 within 10% of linear | **FAIL** | A 1.02, C 1.01, D 1.005, **B 1.23** |
| P6 | learned observers (memory) s_50 >= 15% above linear | **FAIL** | A 1.02, C 1.01, D 1.005; B 1.24 (= memoryless) |
| P7 | linear rule follows the transfer operator, hazard slope ~1 | PASS | max deviation .005; slopes 1.00-1.02 |
| P8 | observers' hazard slope in eta >= 1.5 | **FAIL** | .99-1.08 (memoryless .99-1.09) |
| P9 | emergence-world failure point is not s_c from drift bounds | PASS | s_50 full 6.82, five 7.85 vs 5.05 |

**Post-dev expectations (not scored, stated before the confirm):** Q1 held (B 1.23 and 1.24; others within 5%). Q2 held (slopes .99-1.09).
Q3 held: the evolved one-message-memory tables found no invariant set in C or D at any M, in any seed.

## What this shows
1. **The counting threshold is exact for the worst case and for learners.** M* = ceil(a/(1-d)), computed from a and d alone, was where
   the theory controller and, in 11 of 12 cell-seeds, the evolved tables first became worst-case safe. The D miss (8 in one seed) is a
   search failure above the bound, not a violation: nothing ever got below it.
2. **Below M* there is essentially no average-case rescue.** Random (uniform) noise gives survival to T=200 of about 0 at M*-1 in A, B, C,
   and .06 in D. P3, the claim that average-case survival would make the worst-case bound look pessimistic, is falsified here.
3. **Above the reading-error threshold s_c, the linear rule is optimal only where d is large relative to 1-a s.** In cell B (d = .1) evolved
   nonlinear rules keep 50% survival to 1.23 s_c; elsewhere they gain 0.5-2%. The theorem says nothing about this region; the closed form
   for the linear rule predicted its curve to within .008.
4. **Memory added nothing measurable** in S2 or S3, and the one-message memory tables of S1 were harder to evolve, not easier.
   P6 and P8 (memory should help) are falsified for this world and these agents. Consistent with the Lean result (KnownStart) that memory
   does not lower the worst-case count; it is not a proof that memory never helps in other worlds.
5. **The emergence world (P9).** Drift-bound s_c = 5.05; observed s_50 6.8 (8-unit evolved net) and 7.85 (five-organ agent).
   The five-organ agent is more robust to sensor error than the evolved net (all three seeds), but the threshold from the linear analysis
   does not transfer to a world with saturating actions and Gaussian noise. Directional prediction only.

## Limits
Scalar linear world; one evolutionary search per arm; "memory" = one previous message or a learned linear predictor with an innovation cut.
"bang" noise is random sign at full size, not an adversary; the invariant-set check is on a grid (conservative). Nothing here is about real systems.
