# Results: stochastic recursive viability (confirmatory run)

Pre-registration: `PREREG_stochastic_2026-11-23.md` (sha256 `25597ec4…a0e0`), frozen
2026-11-23 09:55:16 UTC together with the four scripts. Log: `confirm_run.log`.
Raw output: `stoch_confirm_raw.json` (3.30 MB). Analysis outputs:
`stoch_confirm_results.json`, `indep_confirm.json`, `real_confirm.json`.

One run, no re-parameterisation after the freeze. Seed base 2000, 600 environments not
seen in dev (seed base 1000, 200 environments), a different scaling grid (X ∈ {5, 7, 10},
adding uniform, t5 and AR(1) shocks), and the held-out second half of each real series.

## Integrity

| Check | Result |
|---|---|
| `stoch_sim.py` hash vs frozen | `331a628b…a39f` — match |
| `analyze.py`, `indep_sim.py`, `real_env.py`, prereg | all four match |
| Script hash recorded inside the raw output | `331a628b…` — same file that was frozen |
| Run metadata | `mode=confirm`, `n_env=600`, `seeds=16`, `atlas=list600`, `scaling=list30`, `pop=list192`, `cheb=list4` |
| Runtime | 95,218.6 s total = 26 h 27 m; `scaling done` 95,118 s, `pop done` +101 s |
| Machine | 8 GB RAM with 8–10 GB swap in use; the runtime is a property of this box, not of the model |

### Dev baseline provenance

The Dev column in the scorecard and in the prereg is `stoch_dev_results.json`. That file is
reproducible: running the frozen `analyze.py` on `stoch_dev_raw.json` in a scratch copy
gives zero differing values across the whole record. The `dev_run2.log` kept beside it
prints a different pass pattern (H6, H9, H10b, H11 and H12 as False); that log came from an
earlier version of the scoring code, and it is not the dev baseline. Compare against the
JSON, not the log.

The 26-hour figure is the scaling grid alone. At 60 s for the cheapest measured cell and
>11 min for the most expensive, 30 cells with no progress output accounts for the whole
interval; `pop` (192 cells) then took 101 seconds because every cell early-exits once all
lanes are dead. There was no hang: the log advanced only at phase boundaries by design.

## Scorecard

**16 of the 21 rows pass; 18 of 23 scored criteria pass** if H5's and H14's two stated
clauses are counted separately, which is the only reading that reconciles the prereg's
"23 scored tests" with its 21-row table. The failing set is the same five rows either way:
H4b, H7, H8, H10a, H12.

| ID | Prediction (short) | Confirm value | Verdict | Dev |
|---|---|---|---|---|
| H1 | Brake helps under delay, hurts without | delay g≥1 **+0.365** [+0.307, +0.430]; no delay **−0.286** [−0.314, −0.259] | **PASS** | pass |
| H2 | Brake value under delay rises with g | Spearman **0.669**, p = 1.6e-40 | **PASS** | pass (0.71) |
| H3 | Worst-case ≠ average-case necessity, both ways | **53.7%** of worst-case-necessary pairs are not average-case; **627** pairs the reverse | **PASS** | pass |
| H4a | ttd ∝ X²/a² | log-log slope **0.945** (SE 0.011), rule 1 ± 0.15 | **PASS** | 0.90 |
| H4b | ttd ≈ C·X²/(a²·f(ρ)), C = 1.0 fixed | **2 of 30 cells outside [0.75, 1.25]**, both ρ = 0.8 | **FAIL** | pass, gauss only |
| H4c | Persistent shocks survive longer | holds in every cell | **PASS** | not tested |
| H5 | Chebyshev holds iid, fails AR(0.8) | **0** iid violations; **2** AR(0.8) violations | **PASS** | pass |
| H6 | M without W hurts; slow EMA helps; M×W > 0 | −0.054 [−0.070, −0.039]; −0.049 vs −0.054; interaction **+0.031** [+0.018, +0.044] | **PASS** | **fail** |
| H7 | Watcher value falls with q_miss | Spearman **0.0007**, p = 0.989 | **FAIL** | fail |
| H8 | S×P < 0, less so as K grows | −0.115 [−0.134, −0.097]; Spearman(K) **0.040**, p = 0.408 | **FAIL** | fail |
| H9 | Resource competition honest for χ ≤ 0.5 | all cells | **PASS** | pass |
| H10a | Unbraked unit raises others' deaths with χ | Spearman **−0.662**, p = 3.1e-07 | **FAIL, reversed** | fail, reversed |
| H10b | Coupling rescues a failed unit | u0 death **0.115** at χ=0.5, **0.880** at χ=0 | **PASS** | pass |
| H10c | Strong coupling kills everyone | others-death **0.974** at χ=0.8; 0.000 at χ≤0.2 | **PASS** | pass |
| H11 | After Brake failure, ttd falls with g | Spearman **−0.766**, p = 6.7e-13, n = 61 | **PASS** | pass |
| H12 | Brake-first beats Watcher/Memory-first | **0.068** [0.039, 0.102] vs **0.126** [0.076, 0.181]; diff **−0.058** | **FAIL, reversed** | pass (n = 5/10) |
| H13a | Real-data rankings stable | VIX **0.644**, DTWEXBGS **0.523** (n = 108 each) | **PASS** | **fail** (0.35, 0.45) |
| H13b | Real-data Brake sign transfers | VIX +0.553 / −0.214; DTW **+0.597** / −0.239 | **PASS** | pass |
| H13c | Real inter-failure interval predicted | VIX 1.98 / 1.59 / 1.55; DTW 1.21 / 1.10 / 0.99 (X = 4, 6, 8) | **PASS** | pass |
| H13d | Cheapest ≥0.9 config holds on test | VIX **1.000** (108/108); DTW **0.9375** (90/96) | **PASS** | pass |
| H14 | Independent re-implementation identical | **4440 / 4440** lanes identical; max variance error **4.04%** | **PASS** | pass |

## Detail

### Brake and the phase boundary (H1–H3)

The sign reversal survives new seeds: the Brake is worth +0.365 under delay with g ≥ 1 and
costs −0.286 without delay. The phase diagram puts the crossing where the theory does:

| delay | g = 0.7–0.8 | 0.8–0.9 | 0.9–1.0 | 1.0–1.1 | 1.1–1.21 |
|---|---|---|---|---|---|
| 0 | −0.266 | −0.285 | −0.301 | −0.284 | −0.295 |
| 1 | −0.153 | −0.092 | **+0.108** | **+0.348** | **+0.380** |

So the Brake is harmful below g ≈ 0.9 and strongly helpful above 1.0. H2's Spearman of
0.669 is this table's monotone part.

Necessity notions still diverge. Of the 218 (environment, organ) pairs that are
worst-case necessary, 117 (53.7%) are not average-case necessary; 627 pairs go the other
way. Only 282 of 600 environments admit any worst-case viable configuration at all, which
is why the worst-case column is thin.

| Organ | wc & avg | wc & ~avg | ~wc & avg | ~wc & ~avg | practical (ρ=1) | avg & ~practical |
|---|---|---|---|---|---|---|
| Skin | 27 | 39 | 172 | 362 | 140 | 86 |
| Memory | 6 | 14 | 88 | 492 | 36 | 59 |
| Spotlight | 34 | 40 | 200 | 326 | 140 | 113 |
| Brake | 33 | 22 | 108 | 437 | 98 | 45 |
| Watcher | 1 | 2 | 59 | 538 | 21 | 39 |

### Diffusion and variance (H4, H5)

The diffusive law holds: slope 0.945 ± 0.011 against a rule of 1 ± 0.15, and the frozen
constant is C = 0.989. H4b is where it breaks: 28 of 30 cells are inside [0.75, 1.25], and
both failures are at ρ = 0.8 and X = 5 — ratio 0.719 (a = 0.5) and 0.747 (a = 1.0). The
observed times are *shorter* than predicted, so the frozen f(ρ) over-corrects at strong
persistence and small X. Two cells is a boundary failure, not a collapse of the law, but
by the registered rule it is a fail.

The Chebyshev theorem behaves exactly as the Lean statement says it should: zero
violations under iid shocks, two under AR(0.8). Variance checks against the closed form:

| Cell | Simulated | Exact | Rel. err |
|---|---|---|---|
| brake, ρ = 0 | 2.922 | 2.963 | 1.4% |
| no brake, ρ = 0 | 205.62 | 200.00 | 2.8% |
| brake, ρ = 0.5 | 6.531 | 6.519 | 0.2% |
| brake, ρ = 0.8 | 10.425 | 10.864 | 4.0% |

The iid variance is inflated 3.5× at ρ = 0.8 (10.4 vs 2.96), which is precisely why the
iid bound stops binding there.

### Memory, Watcher, Skin, Spotlight (H6–H8)

**H6 flips to pass.** In dev the M×W interaction CI included zero. Now: Memory without a
Watcher costs −0.054 [−0.070, −0.039]; a slow EMA reduces that to −0.049, and among
environments with an EMA the marginal value of Memory rises with the EMA rate (+0.180,
p = 0.0093); the M×W interaction is +0.031 [+0.018, +0.044]. Memory and Watcher are
complements under regime shifts, as the theory said.

**H7 fails again, and not marginally.** Watcher value given Memory under shifts has
essentially no relationship to q_miss: 0.0007, p = 0.989. Two independent runs, 800
environments, no signal. Either the miss probability is absorbed by the rest of the
configuration, or the value of the Watcher is set by latency and false alarms rather than
misses. The prereg kept the prediction unchanged so that this would be decisive; it is.

**H8 fails on the same half as in dev.** Skin and Spotlight are substitutes
(S×P = −0.115, CI excludes zero) at every latency, but the substitution does not weaken
with K: −0.127, −0.101, −0.116, −0.118 across K = 1–3 … 10–12, Spearman 0.040, p = 0.408.
The exploratory `phase_SP_by_K` table shows the same flatness. Substitution here is a
property of what the two organs do, not of how slow the Watcher is.

The exploratory Watcher-by-latency table is also flat and slightly negative in every bin
(−0.007 to −0.023), and every bin's interval includes zero (the narrowest is K = 7–9,
[−0.050, +0.003]). Given Memory, an *additional* Watcher is close to worthless in this
parameterisation regardless of latency — consistent with H7's null.

### Coupling and resources (H9–H12)

The coupling story is the clearest thing in the run, and it is not the story the
`CoupledPartial` intuition suggested:

| χ | u0 death (one unbraked) | others dead given u0 dead | aggregate survival, one unbraked | control |
|---|---|---|---|---|
| 0.0 | 0.880 | 0.000 | 0.741 | 1.000 |
| 0.2 | 0.714 | 0.0001 | 0.997 | 1.000 |
| 0.5 | 0.115 | 0.000 | 1.000 | 1.000 |
| 0.8 | 0.441 | 0.443 | 0.557 | 0.028 |

Coupling **rescues** the failing unit (u0 death 0.880 → 0.115 as χ goes 0 → 0.5) and only
at χ = 0.8 does it turn into a shared fate that kills the control population too. That is
H10b and H10c passing, and it is also why H10a reverses: among zombie cells (ratio ≥ 1),
higher χ means *fewer* other-unit deaths (−0.662, p = 3e-7). The "one unbraked unit
contaminates its neighbours" reading is wrong in this model; the dominant effect is
neighbour support. H10a and H10b are two views of the same mechanism, and the paper should
say so rather than reporting them as separate findings.

H9 is evaluated only on χ ≤ 0.5, as registered: every cell with ratio ≥ 1.5 has alive
fraction ≥ 0.999, and every cell below 1 stays within the ratio + 0.05 envelope. The
χ = 0.8 collapse is not an H9 violation — it is the H10c prediction.

**H12 is the result that changes a claim.** With scarce income, delay and g ≥ 1, funding
the Brake first is *worse* than funding Watcher and Memory first: 0.068 [0.039, 0.102]
versus 0.126 [0.076, 0.181], difference −0.058 against a rule requiring > +0.05. Dev had
said the opposite, on n = 5 versus 10 configurations — the run is now at 30 versus 32, and
the sign is the other way. The prereg labelled H12 "dev-informed" exactly so that this
could happen; the funding-priority claim needs rewriting, not patching. The mechanical
reason is visible in the failure-response table: under delay with g ≥ 1, removing the
Brake is catastrophic (−0.930 [−0.974, −0.874]), but that is the value of a Brake you
already have, not of one you buy before Memory and Watcher.

### Real data (H13)

Both series use half 1 for calibration and half 2, unread in dev, for test.

| | VIXCLS | DTWEXBGS |
|---|---|---|
| n cal / test | 1084 / 1083 | 1059 / 1059 |
| sd cal | 0.0880 | 0.00297 |
| ρ̂ cal / test | −0.095 / −0.066 | +0.076 / +0.033 |
| H13a median Spearman | **0.644** | **0.523** |
| H13b Brake, delay / no delay | +0.553 / −0.214 | +0.597 / −0.239 |
| H13c ratio, X = 4 / 6 / 8 | 1.98 / 1.59 / 1.55 | 1.21 / 1.10 / 0.99 |
| H13d cheapest-config holdover | 108/108 = **1.000** | 90/96 = **0.9375** |

H13a is the reversal worth recording: rank stability *failed* in dev (0.35, 0.45 on
within-half-1 splits) and *passes* on half 2, which was never read during development. The
dev split stayed inside one regime; the confirm split crosses regimes, and the ranking
holds across the crossing.

H13c passes but the VIX ratios sit at the top of the band (1.55–1.98, all above 1), so on
VIX the model systematically under-predicts how long the no-organ loop survives between
failures. That is a bias, not noise, and it should be stated with the pass.

### Implementation check (H14)

The independent scalar re-implementation reproduces **4440 of 4440** lanes exactly, and the
closed-form covariance-sum variance matches simulation to ≤ 4.04% (worst cell: ρ = 0.8).
This is a check on the code, not on the theory, and it is clean.

## Exploratory results

**Practical necessity** (gap in V = survival − ρ_cost·cost/income, rate ρ_cost):

| Organ | ρ = 0.5 | ρ = 1 | ρ = 2 | average-case | worst-case |
|---|---|---|---|---|---|
| Skin | 0.270 | 0.233 | 0.147 | 0.332 | 0.110 |
| Memory | 0.088 | 0.060 | 0.023 | 0.157 | 0.033 |
| Spotlight | 0.300 | 0.233 | 0.132 | 0.390 | 0.123 |
| Brake | 0.193 | 0.163 | 0.100 | 0.235 | 0.092 |
| Watcher | 0.057 | 0.035 | 0.008 | 0.100 | 0.005 |

Ranking is stable across all three cost rates: Spotlight ≈ Skin > Brake > Memory >
Watcher. Memory and Watcher are the expensive organs, and the Watcher is nearly never
worth its cost at any rate. That is the same conclusion H7 reaches from the other side.

**Cost of viability.** 78.5% of environments admit some configuration reaching 0.9
survival. Among the cheapest such configurations:

| Class | Skin | Memory | Spotlight | Brake | Watcher |
|---|---|---|---|---|---|
| delay | 0.483 | 0.218 | 0.502 | 0.464 | 0.133 |
| no delay | 0.277 | 0.031 | 0.273 | **0.000** | 0.008 |

Skin (~48%) or Spotlight (~50%) appears in about half of the delay-class cheapest sets,
the Brake in ~46%. Without delay the Brake is never in the cheapest viable set — a clean
confirmation of H1 from the cost side.

**Failure response** (drop in survival when one organ is removed mid-run; delay, g ≥ 1):

| Organ | Drop | Median ttd after |
|---|---|---|
| Brake | **−0.930** [−0.974, −0.874] | 94.0 |
| Memory | −0.232 [−0.318, −0.152] | 107.1 |
| Spotlight | −0.225 [−0.313, −0.142] | 162.0 |
| Watcher | −0.193 [−0.270, −0.121] | 153.6 |
| Skin | −0.060 [−0.121, +0.003] | 189.7 |

Removing the Brake under delay kills almost everything, and fast. Removing Skin is
statistically indistinguishable from doing nothing on this measure — Skin's value is in the
cost accounting and in the cheap-viable sets, not in acute failure response.

## What this run changes

**Newly supported, previously failing:** H6 (M×W complementarity) and H13a (real-data rank
stability). Both were dev failures that the confirmatory run overturns with more data or
better splits.

**Refuted with adequate power, must be rewritten:** H12. The funding order claim is
backwards at n = 30/32. Any text saying "fund the Brake first under scarcity" has to go.

**Reversed twice, mechanism mis-described:** H10a. Spillover rescues rather than
contaminates; report it together with H10b, not as a separate zombie-mode finding.

**Replicated failures:** H7 and H8's second part. Two runs, 800 environments, no signal in
either. These should move from "dev-falsified, under test" to "falsified" in the paper, with
the H7 null reported as an informative negative (Watcher value is not governed by miss
probability) rather than as a loose end.

**Boundary failure:** H4b at ρ = 0.8, X = 5. The frozen constant is right for iid, uniform
and t5, and drifts by 25–28% for strongly persistent shocks at the smallest threshold. If a
sharper f(ρ) is wanted it must come from a new pre-registration, not from refitting this
one.

## Limits

- Linear scalar loop with additive organ effects; "organ capacities" are parameterised
  abstractions.
- Survival is the only criterion; no cost for time spent near the boundary.
- Lean covers the iid variance and Chebyshev statements only. H4's constant, H10, H11's
  root scaling and H12 are simulation findings.
- 23 scored criteria by the prereg's count, no multiplicity correction. Pass rules are
  effect-size and sign rules, not significance claims, so "18/23" is a descriptive count.
- The prereg's prose says "23 scored tests" while its table has 21 rows. The 18/23 above
  counts H5's and H14's two stated clauses separately, which is the most likely
  reconciliation but is an inference, not something the prereg spells out. The five failing
  rows (H4b, H7, H8, H10a, H12) do not depend on the convention. This note exists so the
  prereg is not "corrected" later to match.
- The freeze is local-only. Ordering rests on the hashes in `FROZEN_stochastic.sha256` and
  on this record, not on a third-party timestamp.
- The real-data agent is simulated. Nothing here is evidence about any real organisation.

## Reproduction

```
cd analysis/coupled_stochastic
/Users/shehzad/Desktop/five-organ-theory/.venv/bin/python stoch_sim.py confirm   # 26 h
/Users/shehzad/Desktop/five-organ-theory/.venv/bin/python analyze.py confirm
/Users/shehzad/Desktop/five-organ-theory/.venv/bin/python indep_sim.py confirm
/Users/shehzad/Desktop/five-organ-theory/.venv/bin/python real_env.py confirm
```

The plain `python3` on this machine lacks numpy and radcad; the venv interpreter is
required. Dev artefacts (`stoch_dev_raw.json`, `stoch_dev_results.json`,
`indep_dev.json`, `real_dev.json`) are kept for the comparison columns above.
