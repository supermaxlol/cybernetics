# Pre-registration: coupled recursive-viability simulation (2026-11-23)

Frozen BEFORE the confirmatory run. Timestamp is local only (file mtime / this text); there is
no public timestamp, so this pre-registration is self-attested.

**Script.** `analysis/coupled/coupled_sim.py`, sha256 `d4ff6fb1b0a21ca3f6ddac9f6e962257ababb7c0244540766ad6d7e001f616ed`.
Confirmatory command: `.venv/bin/python analysis/coupled/coupled_sim.py confirm` (from
`analysis/coupled/`). The script records its own sha256 in the output; a mismatch voids the run.

**What was seen before freezing (disclosed).** Two development runs were made:
- dev seeds 0–11;
- environment draws seeded 101–107;
- the dev (training) parameter ranges.

The design changed after the first dev run:
- (i) micro units no longer die individually; only the aggregate can fail. Before this, frozen
  dead units masked the unstable mode.
- (ii) H4/H5 use regret (continuous) as the primary metric, because survival was at
  floor/ceiling in the few dev shift environments.
- (iii) H9 was re-stated as a monotone-decline test. The original "≤ 10 % survival at f = 0.1"
  was a wrong guess on dev.

Dev results are in `coupled_dev_results.json`. On dev, H5 and H10b were falsified. They are
kept unchanged.

**Held-out design (out-of-sample).**
- New seeds 10000–10039. Micro and partial runs use the first 20 of these.
- New environment draws: seed 202 and up, 20 environments per family.
- Shifted parameter ranges: Θ ∈ [0.5, 2] (dev [0, 1.5]) and X ∈ [2, 10] (dev [1, 8]).
- Families:
  - F: formal-matched; exactly the Lean model.
  - S: stochastic, with Poisson shifts, an estimating Watcher with threshold, and
    deviation-coupled resources.
  - H: heavy-tailed Student-t(3) shocks, which violate the |d| ≤ D assumption.
- All 32 configurations share each seed's exogenous paths (common random numbers).
- T = 2000.

**Hypotheses and falsification criteria.** Lean names refer to `FiveOrgans/Coupled*.lean`.

| id | prediction | source | falsified if |
|---|---|---|---|
| H1 | In F, no formally viable (config, env, seed) run ever dies | `stays_iff`, `viable_iff` (theorem) | any death |
| H2 | In F, formally viable configs survive more often than non-viable ones | worst-case ⇒ typical (empirical) | surv(non-viable) ≥ surv(viable) |
| H3 | In S with delay, configs without Brake survive ≤ 5 % | `brake_necessary`, `unstable_exceed` | > 5 % |
| H4 | In S shift envs with Brake, the M×W interaction contrast on regret is negative (complementarity) | `complementary_MW` | 95 % bootstrap CI upper ≥ 0 |
| H5 | In S shift envs with Brake, Memory without Watcher has higher regret than no Memory | `memory_harmful` (worst case only) | 95 % CI lower ≤ 0 |
| H6 | In no-shift S envs, a too-low Watcher threshold (0.2× nominal) raises regret of M∧W configs | misconfiguration (beyond the Lean model) | 95 % CI lower ≤ 0 |
| H7 | Raising Watcher latency K from 1 to 8 hurts survival of M∧W∧B more without Spotlight than with it | `spotlight_helps`, `similar_not_same` | 95 % CI lower ≤ 0 |
| H8 | Uniform interventions transfer: in F with N = 20 units and η = 0.1, every config that is formally viable with margin η·L₁ keeps the aggregate inside X | `transfer_intervention` (theorem) | any aggregate failure |
| H9 | Partial ablation (fraction f of units lose the Brake under delay) lowers aggregate survival, monotonically in f ∈ {0, .05, .1, .25} | outside `CoupledTransfer` scope (heterogeneous units) | CI of surv(f=.25) − surv(0) upper ≥ 0, or means not monotone |
| H10a | In H, some formally viable configs die (assumption violation) | validity condition | no deaths |
| H10b | In S and in H, the per-environment Spearman ρ between formal margin (X − peak)/X (−10 if unstable) and survival exceeds 0.5 in more than half of the environments | cross-environment generalisation | either family's fraction with ρ > 0.5 is ≤ 0.5 |

**CIs.** Percentile bootstrap, 2000 resamples over environments (seed 7).

**Not hypotheses (descriptive).** Per-configuration means of all metrics: survival, coherence,
recovery, retention, regret, detection, false alarms and amplification. Per-environment lists of
necessary and dispensable capacities in S.

**Interpretation rules fixed in advance.**
- H1 and H8 test the simulator against theorems. A failure means an implementation bug or a
  mis-stated theorem; it is not evidence about the world.
- H2–H7, H9 and H10 are empirical claims about this simulator only. None of them is a claim about
  any real organism, firm or AI system.

No changes to this file after the confirmatory run starts.
