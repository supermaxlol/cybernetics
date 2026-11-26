# Predictions written before any output of sense.py on learned agents was seen (2026-11-26 02:27, local clock)

Only smoke tests of the theory controller, one learned message table (survival not looked at) and the closed forms had been run. A dev
run (seed 700) was in progress with an empty log. Inputs used: a and d only. No threshold is fitted to agents.

| Cell | a | d | M* = ceil(a/(1-d)) | s_c = (1-d)/a | linear rule s_50 / s_c (closed form, grid) | eta = .02 survival, linear rule (operator) |
|---|---|---|---|---|---|---|
| A | 2.0 | .25 | 3 | .375 | 1.07 | .134 |
| B | 1.2 | .10 | 2 | .750 | 1.05 | .505 |
| C | 3.0 | .20 | 4 | .267 | 1.06 | .068 |
| D | 4.0 | .30 | 6 | .175 | 1.08 | .049 |

P1 (theorem, so a check of the code). Below M* no arm, with or without memory, has a nonempty worst-case invariant set; at M* the uniform table has all of it.
P2 (risky). Learned tables without memory reach worst-case invariance (some nonempty set) at M*, or at most one message above it.
P3 (risky). Under random uniform noise, learned tables below M* survive longer than the worst-case theorem would suggest: survival to T > .05 at M* - 1 in at least two cells.
P4. S2, linear rule: survival is exactly 1 for s <= s_c and follows the closed form above it.
P5 (risky). Learned memoryless rules have s_50 within 10% of the linear rule's.
P6 (risky). Learned observers (memory) have s_50 at least 15% above the linear rule's. The theorem's s_c covers memoryless rules only.
P7. S3, linear rule: survival follows the transfer operator; hazard is linear in eta at small eta (no plateau).
P8 (risky). Observers with an innovation cut lose less: hazard log-log slope in eta at least 1.5 (memoryless: about 1).
P9 (risky, directional). In the emergence world, where actions saturate and noise is Gaussian, s_c computed from drift bounds is not the failure point.
