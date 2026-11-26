# Development log, open-world emergence (dev only; nothing here is a confirmed result)

**Dev seed 900** (`emerge.py dev 900`, 80 generations, population 80; `dev_run.log`, `dev_900.json`):
- Mixed world: emerge .855, free .851, full .851, small .859, drift .853, five .997. Hand-made organs ahead by about .14.
- Class 1 (hidden actuator sign with a cue): emerge .248, free .54, five 1.0. Evolved nets ended with one unit and no recurrence.
- Shift test (actuator sign flips halfway): every arm about 0-.14. Agents are fixed within a life, so none re-learns.
- Drift (random selection) fails in classes 0, 1, 4, 5, as it should; selection matters.

**Search-budget check, seed 901** (`dev_long.py`; stopped by a session end after three runs, 2026-11-26 03:07):
- Class 1, emerge: .203 at 80 generations / pop 80; **.918 at 400 / pop 120**, 2 units, cue ablation costs .577.
- Class 1, free at 80: .162.
- So the dev-900 gap between evolved and hand-made agents on class 1 was mostly search budget, not inability.
  Consequence for the PREREG: the confirm must use the larger budget, and any "five-organ beats emergence" claim must be stated per budget.

**Open before freezing:** budget for all arms (400/120 costs ~4x per run); the five arm at 400; the mixed world at 400;
risky predictions; score function; seeds. The shift test cannot test reorganisation within a life, because nothing here learns within a life.

**2026-11-26 16:30.** emerge.py (dev, unfrozen): GENS/POP globals; CLI `dev SEED SET GENS POP` writes dev_SEED_SET_gGENS.json. No logic change. Dev at 400/120, seed 902, all 7 sets in parallel.

**2026-11-26 17:10.** Dev 902 at 400/120 done (`dev_902_*.log`). Seen before any PREREG:
- mix: five .978; emerge .866, free .87, full .86, small .869; drift .47.
- c1: emerge .392 (seed 901 gave .918), free .202, full .849, small .286, five 1.0 (memory gate, ablation .858).
- c0, c4, c5: emerge 1.0 with one unit. c2, c3: emerge .93/.925; full .928/.839.
- five gates: c1 memory; c4 brake (ablation .899); c2 brake only (no watcher); c3 and c5 no organs; c0 spotlight on but ablation 0.
- drift below emerge in every set. Shift (late survival after actuator flip) <= .283 everywhere.
- Change (before any new results): `measure` adds `gen`, `gen_other`, `gen_by_class`: the evolved genome tested in a fresh world with all
  six classes (rng [seed, 997]). Dev seed 903 at 400/120 to check it and to see a second seed at the confirm budget.

**Correction.** The entry headed 17:10 was written at about 16:56 (dev 903 logs start 16:56-16:58); 17:10 was a guess, not a clock reading.

## 18:25 dev 903 complete; predictions written
- Dev 903 (400 gens / pop 120) finished at about 18:20. Table: `dev_903_*_g400.json`.
- c1 differs from 902: emerge .861 (902: .392), free 1.000 (902: .202). c1 is seed-fragile for evolved nets.
- Generalisation (new field): every net evolved on a single class other than c1, and every mix-evolved net, survives about .16-.22 on the
  hidden-sign class. The five arm survives 1.0 there.
- `emerge_score.py` was written after seeing dev 902 and dev 903. Thresholds were chosen from those two seeds plus 900/901,
  so its 12/12 pass on dev 903 is calibration, not evidence.

## 22:56 confirm complete
11 of 12 (E4 fails). Full write-up in `RESULTS_emergence_2026-11-26.md`. Frozen hashes re-checked OK.
