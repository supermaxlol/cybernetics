# Results: coupled extension, confirmatory run (2026-11-23)

Pre-registration: `PREREG_coupled_ext_2026-11-23.md`. Its timestamp is local only.

Hashes:
- script `coupled_ext.py` sha256 49974124…3b3829 (frozen before confirm);
- base `coupled_sim.py` d4ff6fb1…f616ed (unchanged).

Run: seeds 20000–20039, 20 held-out environments per test, 89.7 s. Raw output:
`coupled_ext_confirm_results.json`, `coupled_ext_confirm_rows.json.gz`,
`confirm_ext_run_2026-11-23.log`.

**10 of 11 supported; 1 falsified (E3a).** All intervals are 95% per-environment bootstrap CIs.

| | Prediction | Estimate [95% CI] | Verdict |
|---|---|---|---|
| E1a | no delay: resist(B) − resist(¬B) < 0 | −0.61 [−0.64, −0.58] | supported |
| E1b | delay: resist(B) − resist(¬B) > 0 | +0.16 [0.13, 0.19] | supported (sign flip) |
| E2a | F, M∧W: adaptation time = latency exactly | 4,741 records, 0 violations | supported (hard test) |
| E2b | S, M: adapt(W) − adapt(¬W) < 0 | −96 [−123, −70] steps | supported |
| E2c | S, M∧W: adapt(P) − adapt(¬P) < 0 | −29 [−44, −17] steps | supported (failed in dev) |
| E3a | C(S ← P) > 0 | +0.016 [−0.006, 0.045] | **FALSIFIED** |
| E3b | Brake failure under delay: Δ survival < 0 | −0.46 [−0.64, −0.29] | supported |
| E3c | Skin failure: Δ false alarms > 0 | +0.033 [0.018, 0.051] | supported |
| E3d | Spotlight failure: Δ adaptation time > 0 | +2.75 [0.05, 5.58] | supported (barely; failed in dev) |
| E3e | Watcher failure: Δ retention < 0 | −0.12 [−0.17, −0.07] | supported |
| E4 | mixtures of viable configs: 0 aggregate failures | 576 cells, 11,520 runs, 0 deaths | supported (hard test) |

## Readings
- **The Brake trades feedback margin for delay robustness (E1).**
  - Without delay it cuts tolerance from δ ≈ 0.69 to 0.08. The theorem `brake_resistance_nodelay`
    predicts tolerance below ¼ vs below 1. Survival is measured at ≥ 0.9, so the simulated values
    sit inside those bounds.
  - Under delay, no unbraked config tolerates even δ = 0.
  - So "the Brake is good" depends on the environment, as `role_flip` states.
- **Adaptation (E2).**
  - The exact latency theorem held in all 4,741 matched cases.
  - In the noisy family, the Watcher shortens adaptation by about 96 steps and the Spotlight by
    about 29 more.
  - Caveat: without Memory, the adaptation metric is meaningless. The error is θ itself and hits
    the band only by chance, so the configs "-" and "W" show 70 steps. E2b and E2c therefore
    condition on M.
- **Failure propagation (E3).**
  - Pathways confirmed: Skin → Watcher (more false alarms), Spotlight → Watcher (slower
    re-anchoring), Watcher → Memory (lower retention).
  - Brake failure is by far the most lethal on average: Δ survival −0.23. The next is the
    Watcher at −0.06.
- **Compensation (E3a falsified; descriptive matrix).** C(o ← o′) is the survival change from losing
  o with o′ present, minus the same with o′ absent. Entries whose CI excludes 0:

  | Failed | Present | C | Reading |
  |---|---|---|---|
  | Brake | Skin | +0.085 [0.013, 0.176] | Skin compensates for Brake loss: lower shock amplitude keeps the loop inside X for longer |
  | Watcher | Skin | +0.020 [0.008, 0.032] | compensation |
  | Skin | Watcher | +0.019 [0.010, 0.029] | compensation |
  | Memory | Watcher | −0.092 [−0.148, −0.045] | interference / dependency: losing M is worse when W is there |
  | Watcher | Memory | −0.122 [−0.179, −0.069] | same dependency, other direction |
  | Watcher | Brake | −0.124 [−0.179, −0.072] | losing W is worse in braked configs, which survive long enough to need it |

  - The predicted Skin ↔ Spotlight substitution in failure **did not appear**.
  - The two substitute in the formal deadbeat table (`minimal_deadbeat`: S or P). Mid-run in the
    noisy family, the Spotlight's latency role dominates its damping role.
  - This matrix is descriptive. Only E3a was pre-registered.
- **Partial interventions (E4).**
  - Random heterogeneous mixtures of viable configs never failed, as `partial_viable` requires.
  - The worst-case converse `partial_unstable` (one unbraked unit suffices) was proved, not
    simulated. Average-case runs (H9) degrade gradually instead.

## Limits
- A single model family.
- The compensation matrix compares 20 pairs, so a few spurious ±CIs are expected.
- The resistance grid is coarse (6 values).
- Nothing here is evidence about real organisms or institutions.
