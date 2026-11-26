# Pre-registration: open-world emergence (2026-11-26, local timestamp only)

## What is tested
Evolved controllers (arms `emerge`, `free`, `full`, `small`, `drift`) are compared with the five-organ architecture (`five`). They are tested in
6 single-pressure worlds (c0 noise, c1 hidden actuator sign plus cue, c2 lying sensor, c3 bursts, c4 delay, c5 reactive) and in their mixture (`mix`).
- Code: `emerge.py` (frozen with this file).
- Scoring: `emerge_score.py` (frozen).
- Budget: 400 generations, population 120.
- Measures:
  - base survival;
  - late survival after an actuator-sign flip (`shift`, reorganisation within one life);
  - number of units and cost;
  - ablation effects;
  - generalisation across all 6 classes (`gen`, `gen_by_class`, `gen_other`).
- Claims are about simulated controllers only. They are not claims about experience or about real organisms.

## Dev history (honest)
- Dev seeds 900, 901, 902 and 903 were all seen before this file was written. The thresholds below were chosen from them.
- c1 was strongly seed-dependent in dev: emerge .392 to .918.
- See `DEVLOG_emergence.md`.

## Confirm
- Fresh seeds 910, 911, 912, 913, 914; all 7 sets.
- Command: `python emerge.py confirm SEED SET 400 120`.
- Scored by `python emerge_score.py confirm 910 911 912 913 914`.
- "4 of 5" means at least 4 of the 5 seeds.

## Predictions (score function is authoritative)
- **E1:** in mix, five beats the best evolved net (emerge/free/full/small) by >= .05 in 4 of 5 seeds.
- **E2:** in the mix world, the evolved emerge agent survives <= .35 in class 1 (hidden sign) and five survives >= .9 there, in 4 of 5 seeds.
  The prediction is that evolution in the mixture does not discover the memory function.
- **E3:** in c1, five >= .95 in all 5 seeds, and emerge's median survival is <= .90.
- **E4:** in c1, every emerge/free net with base >= .8 has cue-ablation loss >= .25: an evolved solution uses the cue.
  This fails if no such net exists.
- **E5:** five's gates are task-specific:
  - c1: memory gate on and memory-ablation loss >= .5, in 4 of 5 seeds;
  - c4: brake gate on and brake-ablation loss >= .5, in 4 of 5 seeds.
- **E6:** the naive organ mapping fails. These organs are not needed for their "own" pressures, in 4 of 5 seeds each:
  - c2 (lying sensor): watcher gate off or watcher ablation < .05;
  - c3 (bursts): skin ablation < .05.
- **E7:** in c0, c2, c3, c4 and c5, emerge is within .05 of the 8-unit full net with <= 2 units, in at least 22 of 25 seed-set cells.
- **E8:** drift (no selection) < emerge in every set, in 4 of 5 seeds.
- **E9:** mean units, emerge < free.
- **E10:** no reorganisation within a life:
  - the median `shift` over sets and arms is <= .15 in every seed;
  - five's shift is <= .15 everywhere.
- **E11:** generalisation, in 4 of 5 seeds for each part:
  - the mean `gen` of the c0-c5 specialists < the `gen` of the mix-evolved emerge agent;
  - five's mix `gen` >= the best evolved net's mix `gen` + .05.
- **E12:** evolved nets from c0, c2, c3, c4 and c5 survive <= .35 on class 1 in >= 95% of seed-set-arm cells.
  This means nothing evolved without hidden-sign pressure handles the hidden sign.

## What would count against the theory
- **E1/E2/E11 failing:** evolved nets match the five arm without a memory organ. The architecture would then be no better than unconstrained evolution.
- **E5 failing:** the five arm's gates are not tied to the pressures.
- **E6** is a pre-registered falsification of the naive organ-per-pressure mapping. If E6 passes, the naive mapping is refuted.
- **E10 passing** means the experiment cannot test within-life reorganisation. That is a limitation to report, not a success.
- **Not tested here:** recognising that a representation is inadequate. The shift test measures it only indirectly, and the dev runs showed none.
