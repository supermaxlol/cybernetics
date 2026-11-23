# Results: coupled recursive-viability simulation (confirmatory, 2026-11-23)

**Run details.**
- Command: `coupled_sim.py confirm`.
- Script sha256 `d4ff6fb1…16ed`. It matches PREREG_coupled_2026-11-23.md, and both files were made
  read-only before the run.
- Runtime: 114 s.
- Raw outputs:
  - `coupled_confirm_results.json`
  - `coupled_confirm_rows.json.gz`
  - `confirm_run_2026-11-23.log`
- Held-out design: seeds 10000–10039; 20 new environments per family; shifted parameter ranges.
- The pre-registration timestamp is local only (self-attested).

## Pre-registered hypotheses

| id | result | numbers | verdict |
|---|---|---|---|
| H1 theorem ⇒ simulator (F) | 10,840 formally viable runs, 0 deaths | — | **supported** (no falsifying instance) |
| H2 viable > non-viable (F) | survival 1.000 vs 0.312 | — | **supported** |
| H3 no Brake under delay ≤ 5 % (S) | 6.4 % survive | — | **FALSIFIED** |
| H4 M×W complementarity, regret (S) | −0.76 [−1.58, +0.12] | survival contrast +0.08 [−0.07, +0.22] | **FALSIFIED** (CI includes 0) |
| H5 Memory without Watcher has higher regret than no Memory (S) | +0.72 [−0.002, +1.40] | survival −0.19 [−0.31, −0.06] | **FALSIFIED** on primary; direction as predicted |
| H6 too-low Watcher threshold harms M∧W | Δregret +0.081 [0.032, 0.135] | false-alarm rate 0.51 vs 0.00 | **supported** |
| H7 latency hurts more without Spotlight | +0.62 [0.47, 0.75] | — | **supported** |
| H8 uniform intervention transfers micro→macro | 215 cells, 4,300 runs, 0 aggregate failures | — | **supported** |
| H9 partial Brake ablation degrades aggregate, monotone in f | f = 0 / .05 / .1 / .25 → 1.00 / 0.999 / 0.966 / 0.746; Δ −0.29 [−0.41, −0.18] | — | **supported** |
| H10a heavy tails break the guarantee (H) | 49 % of formally viable configs die | — | **supported** |
| H10b formal margin ranks survival (ρ > .5 in > half of envs) | S: median ρ 0.76, 70 %; H: median ρ 0.61, 68 % | — | **supported** |

Score: 8 supported, 3 falsified (H3, H4, H5).

Dev and held-out disagreed twice, which shows why the held-out stage was needed:
- H4 passed on dev and failed on held-out.
- H10b failed on dev and passed on held-out.

## What the falsifications mean

**H3.** The no-Brake delayed loop is x′ = x − x₋₁ + w. Its characteristic roots are e^{±iπ/3}, so it
is *marginally* stable, not exponentially unstable.
- The Lean `unstable_exceed` theorem holds for *resonant adversarial* shocks.
- Under random shocks, |x| grows roughly like √t. Runs with a large X (5–10) can last 2000 steps:
  survival reached up to 23 % per environment.
- So "Brake necessary under delay" is a worst-case theorem. In random environments it is a
  statement about horizon length. The 5 % threshold was too strict.
- This explanation is post hoc (exploratory). The falsification stands.

**H4 / H5.**
- `complementary_MW` and `memory_harmful` are worst-case (adversarial shift timing) theorems.
- With random shift timing, a Watcher that has to estimate, and Poisson shift counts, the average
  effects point the predicted way but are not reliable across environments.
- H5's secondary survival contrast does exclude 0, but it was secondary. It does not rescue the
  hypothesis.
- **Mathematical necessity in the worst case did not become reliable empirical necessity on
  average.** This is the main distinction the goal asked for, and it was observed, not assumed.

## Descriptive (not hypotheses; family S, held-out)

- **Brake** is in every near-best configuration (within 0.02 of the best survival) in **15 of 20**
  environments.
- **Memory** is in every near-best configuration in 4 of 20; **Spotlight** in 2; **Watcher** in 1.
- **Skin** is in every near-best configuration in 0 of 20: it was never individually necessary.
- In every environment *some* configuration survived fully, but none of the capacities was
  necessary across all environments. Necessity is environment-relative, as the Lean
  `organ_necessity_relative` says.
- **Substitution:** SMB and MPB have the same survival (0.844) and near-identical regret.
  Skin and Spotlight substitute for each other, as in `substitutable_SP`.
- **Coherence vs survival:**
  - MPBW has the highest coherence (0.999) and the fastest recovery (0.29 steps), but a 0.24
    false-alarm rate and survival of 0.75.
  - MBW has 0.83 survival.
  - Adding a capacity improved one viability metric and worsened another, so "more organs" is not
    monotone (`not_monotone`).
- **All five (SMPBW)** is not at the top on survival in S, because each capacity costs resources.
  This matches `resources_bind`.

## Limits

- One linear scalar loop with a fixed brake gain of 1/4. All results are about this simulator; none
  is a claim about organisms, firms or AI systems.
- The Watcher is a windowed-mean threshold detector. Other detectors may behave differently.
- The H3 explanation, the descriptive tables and the dev/held-out comparison are exploratory.
