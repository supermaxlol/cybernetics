# Results: open-world emergence confirm (2026-11-26)

- Pre-registration: `PREREG_emergence_2026-11-26.md`, frozen at 18:23 local time (`FROZEN_emergence.sha256`; hashes re-checked OK after the run).
- Confirm: seeds 910-914, 7 sets, 400 generations, population 120. Finished at 22:56. Raw output: `confirm_{seed}_{set}_g400.json`; score: `score_confirm.json`, `confirm_score.log`.
- All results are about simulated controllers in this model. None is a claim about real organisms or about experience.

## Score: 11 of 12

| | Prediction | Result |
|---|---|---|
| E1 | five beats the best evolved net in mix by >= .05 | PASS, 5/5 (margins .10-.13) |
| E2 | mix-evolved emerge <= .35 on hidden sign, five >= .9 | PASS, 5/5 (emerge .17-.26, five 1.0) |
| E3 | c1: five >= .95 all seeds, emerge median <= .90 | PASS (five 1.0 x5; emerge .25/.67/.45/.98/.71, median .665) |
| E4 | c1: every evolved net with base >= .8 uses the cue (ablation >= .25) | **FAIL**: 2 of 6 such nets use the cue |
| E5 | five gates task-specific (memory in c1, brake in c4, ablation >= .5) | PASS, 5/5 each (memory .77-.82, brake .89-.90) |
| E6 | naive organ mapping fails: no watcher for lying sensor, no skin for bursts | PASS, 5/5 (both ablations 0) |
| E7 | emerge within .05 of the 8-unit net with <= 2 units (c0, c2-c5) | PASS, 25/25 |
| E8 | drift (no selection) < emerge in every set | PASS, 4/5 (seed 910 fails only by a tie, 1.0 = 1.0 in c0) |
| E9 | mean units emerge < free | PASS (1.14 vs 2.0) |
| E10 | no within-life reorganisation (median shift <= .15) | PASS (median .06-.07; five max .099) |
| E11 | specialists generalise worse than the mix agent; five generalises best | PASS, 5/5 both parts |
| E12 | nets evolved without hidden-sign pressure fail on hidden sign | PASS, 100/100 cells <= .35 |

## Mean base survival over the 5 seeds

| set | emerge | free | full | small | drift | five |
|---|---|---|---|---|---|---|
| mix | 0.854 | 0.849 | 0.856 | 0.863 | 0.375 | 0.979 |
| c0 noise | 1.000 | 1.000 | 1.000 | 1.000 | 0.634 | 1.000 |
| c1 hidden sign | 0.610 | 0.964 | 0.780 | 0.253 | 0.142 | 1.000 |
| c2 lying sensor | 0.970 | 0.975 | 0.976 | 0.969 | 0.660 | 0.914 |
| c3 bursts | 0.950 | 0.963 | 0.921 | 0.964 | 0.559 | 0.973 |
| c4 delay | 1.000 | 0.994 | 1.000 | 1.000 | 0.278 | 1.000 |
| c5 reactive | 1.000 | 0.996 | 0.999 | 1.000 | 0.368 | 1.000 |

- Mean units: emerge 1.14, free 2.0, full 8, five 0.91.
- Mean cost: emerge .014, small .044, full .248, five .009 (free has no unit cost by design).

## What this supports
1. **Which capacity, and when.** The only pressure that separates architectures is the hidden actuator sign.
   - Under that pressure the five-organ agent switches on memory, and removing it costs about .8 survival.
   - Under delay it switches on the brake, and removing it costs about .9.
   - Under noise, bursts, a lying sensor and a reactive world, a single unit is enough. Organs add nothing there.
2. **Cost.** Evolved nets match the 8-unit net in the easy worlds with about one unit, at about 1/18 of the cost.
3. **Evolution in a mixed world does not find the memory function.** All 20 mix-evolved nets survive at most .26 on the hidden sign (E2). The fixed five-organ architecture survives 1.0, which explains its .10-.13 advantage in mix (E1).
4. **Generalisation.** Nets evolved under one pressure do not transfer to the hidden sign (E12: 100 of 100 cells). The five-organ agent generalises best (E11).

## What failed or is limited
- **E4 failed.** When evolved nets do solve the hidden sign, most do not use the cue.
  - Instead, ablations of the previous action (`uprev`, .19-.84) and of recurrence (up to .84) hurt.
  - So the solution is an action-outcome memory: the net infers the sign from what its own last action did.
  - This is a memory function, but not the cue-reading mechanism the five-organ memory uses. The prediction named the wrong mechanism.
- **Post hoc, not pre-registered.** In c1 the cost-free `free` arm (.964) does much better than the cost-penalised `emerge` arm (.610).
  - So the cost of units, not the search, is what usually prevents the solution.
  - This needs its own test before it can be claimed.
- **E6** refutes the naive mapping of one organ per pressure. The watcher is not needed against a lying sensor, and the skin is not needed against bursts.
- **E8**'s single failure is a tie at ceiling in the trivial noise world.
- **E10 passing is a limitation, not a success.** No arm reorganises after the actuator sign flips within a life.
  - The experiment therefore cannot test whether an agent recognises that its representation has become inadequate.
  - The goal's question of telling compression apart from recognising inadequacy is still open.
- **Scope.** Scalar plant, 6 hand-designed pressure classes, a fixed evolutionary budget, 5 seeds. Thresholds were chosen after 4 dev seeds (see DEVLOG).
