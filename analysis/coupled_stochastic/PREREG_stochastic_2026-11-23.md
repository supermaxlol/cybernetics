# Pre-registration: stochastic recursive viability (confirmatory run)

Date: 2026-11-23. **The timestamp is local only.** This file and the scripts were frozen with `chmod 444`, and their SHA-256 hashes were written to `FROZEN_stochastic.sha256` before `stoch_sim.py confirm` ran. No third party timestamped them, so the ordering rests on the file hashes and on the honesty of this record. Nothing else guarantees it.

## Status of the thresholds

The hypotheses come in three kinds:

- **Theory-derived**: predicted from the Lean theorems or the closed-form loop analysis before any simulation.
- **Dev-informed**: thresholds or restrictions changed after the development run (`stoch_dev_raw.json`, seed base 1000, 200 environments).
- **Dev-falsified**: theory-derived predictions that failed in dev. They are kept unchanged so that the confirmatory run tests whether the failure replicates.

Confirmation uses seed base 2000, 600 new environments, a different scaling grid (X ∈ {5, 7, 10}, adding uniform, t5 and AR(1) shocks), and the held-out second half of each real series. No threshold below may change after confirm starts.

## Model (summary; the code is authoritative)

The model has one shared loop, x' = x − k·x_prev + w with delay, or x' = (1 − k)x + w without delay. The disturbance seen by the loop is

  w = θ − m + sf·d + χ·(mean of the other units' x)

- **Shock attenuation:** sf = σ^S·α^P.
- **Brake:** sets k = kB; without it, k = g.
- **Memory:** a slow EMA (rate a_s) plus fast memory. Fast memory is a Watcher window of length L, where L = 1 with the Spotlight and L = K without it.
- **Watcher:** fires on |window mean| > τ_c·sf. It misses with probability q_miss and raises false alarms with probability q_fa.
- **Resources:** R += income − funded organ cost − κ|x|. Organs are funded in priority order, and an organ that cannot be funded is disabled for that step.
- **Death:** |x| > X or R < 0.

Each environment draws all of these from `draw_env`: shock distribution, persistence ρ, regime-shift rate λ, Watcher reliability and latency, delay, feedback strength g, brake gain kB, attenuations, resource levels and costs, and priority. `wc_viable` gives the worst-case verdict; it reproduces the Lean `Coupled.lean` tables exactly (selftest).

## Necessity notions (defined before dev)

For each environment and organ o:

- **Worst-case necessary:** some configuration containing o is worst-case viable, and no configuration without o is.
- **Average-case necessary:** (max survival over configurations with o) − (max survival over configurations without o) ≥ 0.05. Survival is the fraction of 16 seeds alive at T = 1000.
- **Practically necessary:** the same gap computed on V = survival − ρ_cost·(configuration cost / income). The primary rate is ρ_cost = 1; 0.5 and 2 are sensitivity checks.

## Hypotheses (confirm run). Pass rules are exactly those coded in `analyze.py` and `real_env.py`

| ID | Kind | Prediction | Pass rule | Dev |
|---|---|---|---|---|
| H1 | theory | Under delay with g ≥ 1 the Brake helps on average; without delay it hurts | 95% CI of the Brake marginal > 0 (delay, g ≥ 1) and < 0 (no delay) | pass (+0.48, −0.24) |
| H2 | theory | Brake value under delay rises with g (the phase boundary sits near g = 1) | Spearman(g, Brake marginal) > 0, p < 0.01 | pass (0.71) |
| H3 | theory | Worst-case and average-case necessity come apart in both directions | ≥ 20% of worst-case-necessary (env, organ) pairs are not average-case necessary, and ≥ 1 pair is average-case but not worst-case necessary | pass (49%, 187) |
| H4a | theory, dev-informed tolerance | ttd ∝ X²/a² (diffusive escape of the undamped resonant loop) | log-log slope within 1 ± 0.15 (gaussian iid cells) | 0.90 |
| H4b | dev-informed constant | ttd ≈ C·X²/(a²·f(ρ)), with C = 1.0 fixed from dev and f(ρ) = (1 − ρ²)/(1 − ρ + ρ²) | every confirm cell (including uniform, t5, ρ = 0.5, 0.8) within ratio [0.75, 1.25] | pass (gauss only) |
| H4c | theory | Persistent shocks (ρ = 0.8) give *longer* survival than iid shocks of equal variance | holds in every (X, a) cell | not tested in dev |
| H5 | theorem plus limit | The Chebyshev bound (Lean `stable_fail_le`) holds under iid shocks and is violated under AR(1) ρ = 0.8 | 0 iid violations beyond 3 SE, and ≥ 1 AR(0.8) violation | pass |
| H6 | dev-falsified | Under regime shifts: Memory without a Watcher hurts, a slow EMA reduces the harm, and M×W interaction > 0 | all three parts | **fail** (interaction CI includes 0) |
| H7 | dev-falsified | Watcher value (given Memory, under shifts) falls with q_miss | Spearman < 0, p < 0.05 | **fail** (−0.09, p = 0.29) |
| H8 | dev-falsified | Skin and Spotlight are substitutes (S×P < 0), less so as latency K grows | interaction CI < 0 and Spearman(K, S×P) > 0, p < 0.05 | **fail** (second part) |
| H9 | dev-informed restriction | Resource competition: with χ ≤ 0.5, population alive fraction ≤ ratio + 0.05 when ratio < 1, and ≥ 0.9 when ratio ≥ 1.5 | all cells | pass (fails at χ = 0.8, reported as a coupling effect) |
| H10a | dev-falsified (CoupledPartial intuition) | Excess deaths of the other units caused by one unbraked unit rise with spillover χ | Spearman > 0, p < 0.05 (zombie mode, ratio ≥ 1) | **fail, reversed** (−0.68) |
| H10b | dev-informed | Coupling *rescues* a failed unit: u0 death ≤ 0.2 at χ = 0.5, but ≥ 0.8 at χ = 0 | both | pass |
| H10c | dev-informed | Strong coupling destabilises the whole population even with every organ working: control others-death ≥ 0.5 at χ = 0.8 and ≤ 0.02 at χ ≤ 0.2 | all | pass |
| H11 | theory | After a mid-run Brake failure (delay, g ≥ 1), time-to-failure falls with g (loop roots with \|z\|² = g) | Spearman(g, ttd_after) < 0, p < 0.05 | pass (−0.66) |
| H12 | dev-informed reformulation | Under scarce income (organ cost > income) with delay and g ≥ 1, funding the Brake first beats funding the Watcher and Memory first | mean survival over 32 configurations: BSPWM − WMPSB > 0.05 | pass (n = 5 vs 10, underpowered) |
| H13a | theory | Real environments: configuration rankings are stable between calibration and test paths | median Spearman > 0.5, each series | **fail** (0.35, 0.45 within half 1) |
| H13b | theory | Real environments: the Brake sign transfers (> 0 delay, g ≥ 1; < 0 no delay) on the test path | both signs, each series | pass |
| H13c | theory plus dev constant | Real environments: the mean inter-failure interval of the no-organ loop on the test path is predicted from calibration (a², ρ̂) | ratio in [0.5, 2] for X ∈ {4, 6, 8}, each series | pass |
| H13d | theory | Real environments: the cheapest configuration with ≥ 0.9 survival on calibration keeps ≥ 0.9 on test | ≥ 70% of agent environments, each series | pass (1.00, 0.875) |
| H14 | implementation | An independent scalar re-implementation gives identical death times; the exact covariance-sum variance matches the simulated variance | 100% identical lanes; relative error < 5% | pass (1480/1480; ≤ 3.2%) |

### Exploratory, not scored

These are reported for the phase diagrams:

- the Brake marginal by (delay, g) bin, which shows where the Brake becomes harmful;
- the Watcher value by latency K, which shows at what latency Memory and Watcher become indispensable;
- the S×P interaction by K, which shows when Skin and Spotlight stop being substitutes;
- the failure-response drop per organ, and the median time to death after failure;
- cheapest-viable-configuration composition (cost of viability);
- practical-necessity rates at ρ_cost ∈ {0.5, 1, 2}.

## Real data (H13)

The real data are FRED VIXCLS and DTWEXBGS, daily, 2018-01-02 to 2026-07. The CSV SHA-256 hashes are recorded in `real_confirm.json`. The environment is real; **the agent is simulated**. Nothing here is evidence about any real organisation or organism.

The transformation is u = Δlog y / sd(calibration), θ = trailing 20-day mean of u, and d = u − θ.

- **Dev:** the first 60% of half 1 against the last 40% of half 1.
- **Confirm:** half 1 against half 2. Half 2 was not read during development.

## Known limits, stated in advance

- **Linear model only:** a scalar linear loop with additive organ effects. Organ "capacities" are parameterised abstractions.
- **Survival is the only criterion:** no cost is attached to the time spent near the boundary.
- **Lean covers only part of the claims:** the stochastic theorems cover variance and Chebyshev bounds for iid shocks only. H4's diffusion constant, H10 and H12 are simulation findings, not theorems.
- **Uncorrected multiplicity:** 23 scored tests and no multiplicity correction. Pass rules are effect-size and sign rules, not significance claims.
