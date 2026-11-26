# Development log, sensor scrambling

**Corrections to the frozen predictions file** (it is not edited). Its header says 02:27; the file was written at 02:25:54. Local clock only.

**Before any dev output on survival was seen** (dev seed 700 running; cells A and B finished computing, nothing printed but run times):
- `sense_score.py` written with the numerical scoring rules for P1-P9.
- Decided for the confirm: add 1.05 and 1.3 to MULT, because P5 (10%) and P6 (15%) cannot be resolved on the dev grid near s_c.

**Known limits, stated now.** The invariant-set check is on a 4001-point grid and is conservative. "Memory" in S1 is one previous message only.
Learned agents come from one evolutionary search, so a learned agent falling short is evidence about the search as well as the bound.
"bang" noise means random signs at full size; it is harsher than uniform noise but is not a worst-case adversary.

**2026-11-26 ~10:05.** The first dev run (seed 700) was stopped when the session ended, after cells A and B, before any output was written.
Nothing from it was seen. Changes made then (dev code, before any result): MULT gains 1.05 and 1.3 now rather than at confirm; output
is one file per cell set (`dev_700_A.json` ...) and the emergence world is set "4"; sense_score.py loads by mode and seed. Rerun as five parallel processes.
Emergence-world side note: dev_long seed 901 showed the class-1 failure of evolved agents was search budget (emerge .20 at 80 gens, .92 at 400).

**10:40, dev scored:** 5 of 9 (score_dev_700.json). PREREG written and sense.py, sense_score.py frozen (FROZEN_sensing.sha256). Confirm seeds 7001-7003.

**Confirm scored (16:20):** 4 of 9, RESULTS_sensing_2026-11-26.md.
