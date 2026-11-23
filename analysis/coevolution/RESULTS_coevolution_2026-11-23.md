# Results: co-evolution (endogenous recursive viability)

Confirm run, 2026-11-23:

- 200 seeds per cell, noise keys base 200;
- script sha256 `f9285e08…`, matching `FROZEN_coevolution.sha256` (all four hashes verified after the run);
- pre-registration: `PREREG_coevolution_2026-11-23.md`, frozen at 10:19:50 UTC (local timestamp only);
- formal base: `FiveOrgans/CoupledEndogenous.lean`, 23 results with only standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and no `sorryAx`.

**Score: 11/11 pre-registered tests pass, including the cells outside the dev range** (X = 6, c = 0.2, a = 2·10⁻⁴).

Read this score with three caveats:

1. **Low risk.** The thresholds were set *after* a dev run in which every test passed, so confirm tests replication on fresh noise and new cells. It was never a high-risk prediction.
2. **C1, C4 and C5b check theorems.** They confirm that the code implements the theorem's model and that the conclusion survives noise.
3. **Weak policy contrast.** The two policies, clip and prop, give the same boundaries on the 0.05 drift grid.

## The four results

### 1. Rate threshold (Lean `rate_iff`; C1–C3)

A policy keeps the error inside the band forever **iff** the drift satisfies v ≤ r + ηX, where r is the response capacity and ηX is what niche shaping absorbs.

- **C1:** with no noise, the simulation reproduces this boundary exactly (0 mismatches).
- **C2:** noise lowers the survivable drift. The boundary is the largest v/(r + ηX) with survival ≥ 0.5:

  | X | η | r | s = 0 | 0.05 | 0.15 | 0.3 |
  |---|---|---|---|---|---|---|
  | 4 | 0 | 0.1 | 1.0 | 1.0 | 0.85 | 0 |
  | 4 | 0.15 | 0.1 | 1.0 | 0.9 | 0.75 | 0.55 |
  | 4 | 0.15 | 0.3 | 1.0 | 0.9 | 0.8 | 0.65 |
  | 6 | 0 | 0.3 | 1.0 | 1.0 | 0.95 | 0.85 |
  | 6 | 0.15 | 0.3 | 1.0 | 0.95 | 0.85 | 0.75 |

  The deterministic threshold is an **upper bound**. In noise, staying viable takes slack over it, and the slack needed grows with s/X.

- **C3:** shaping the niche raises the survivable *absolute* drift v* under heavy noise (s = 0.3). For X = 4 and r = 0.1, v* rises from 0 (no shaping) to 0.385 at η = 0.15. For X = 6 and r = 0.3, it rises from 0.255 to 0.90.

  Shaping has a smaller effect on the *ratio* to the noiseless threshold, because the threshold itself grows with η.

### 2. Depletion (Lean `depletion_kills`, `static_not_recursive`; C4)

When using the environment depletes its capacity to regenerate (β > 0), every agent dies from any starting stock:

- all 72 statically viable depleting cells died (q₀ ≥ c);
- mean time to death was 0.973–1.004 × the closed-form t*;
- with β = 0 and q₀ > c, survival was 1.0.

**Static viability does not imply recursive viability.** No organ configuration rescues this; only a change in consumption or regeneration does. The model has no organ that can do either.

### 3. The cost of keeping up (Lean `response_lower`, `afford_impossible`, `accel_impossible`; C5, C5b, C6)

The environment accelerates (v = v₀ + a·t) and the agent buys capacity r = r₀ + b·t from a finite budget.

- **C5b:** every cell dies, as the theorem says.
- **C5:** mean time to death has an **interior maximum** in b in all 6 (a, s) cells. Under-investing dies of drift and over-investing dies of the budget.

Mean time to death (s = 0.05) for b = 0, 0.5, 1, 2, 3 and 5 (×10⁻⁴):

| a | ttd | best b |
|---|---|---|
| 1·10⁻⁴ | 2422, **4769**, 3563, 2001, 1459, 1001 | 0.5·10⁻⁴ |
| 2·10⁻⁴ | 1233, 1626, **2412**, 2001, 1459, 1001 | 1·10⁻⁴ |
| 3·10⁻⁴ | 835, 999, 1235, **2001**, 1459, 1001 | 2·10⁻⁴ |

- **The best investment rate tracks the acceleration**, at roughly b* ≈ a/2 to 2a/3 on this grid.
- **C6:** the deterministic recursion predicts the noisy mean time to death within 5% (ratios 0.950–1.000).

### 4. Ultrastability (Ashby; C7–C10)

The environment alternates at rate λ between two regimes:

- regime A (delay, g = 1): the Brake is required;
- regime B (destabilising feedback): the Brake is fatal.

Survival with no refractory period (m_d = 1), selected cells:

| λ | τ | fixed Brake | fixed no-Brake | ultrastable | oracle | switches |
|---|---|---|---|---|---|---|
| 0.001 | 2 | 0.07 | 0.09 | 1.00 | 1.00 | 4 |
| 0.01 | 2 | 0 | 0.15 | 1.00 | 1.00 | 24 |
| 0.01 | 4.5 | 0 | 0.10 | 0.91 | 1.00 | 72 |
| 0.03 | 1 | 0 | 0.64 | 0.97 | 1.00 | 215 |
| 0.03 | 4.5 | 0 | 0.66 | 0.92 | 1.00 | 89 |

- **C7:** ultrastable survival is at least 0.91 everywhere and beats the better fixed configuration in all 20 cells. The margin is 0.26 at minimum and 0.75 on average.
- **C8:** a 5-step refractory period after each switch costs 0.27 survival on average.
- **C9:** the oracle is never beaten.
- **C10:** a lower switching threshold τ means more chattering (Spearman −0.73, p = 0.0003). At τ = 0.5 there are about 800 switches, with no loss of survival.

**When the environment changes which capacity is fatal, no fixed configuration is viable.** A trial-and-error reconfiguration rule that knows nothing about the regime recovers almost all of the oracle's performance. This answers the question the 32-configuration analysis could not reach: the capacity needed is the capacity to *change configuration*, triggered by an essential variable leaving its band.

## Falsified or weakened claims

- **No pre-registered C-test failed.** The dev run, before thresholds were set, did not falsify any hypothesis either.
- **The clip/prop contrast was uninformative.** The proportional controller does as well as the theorem's optimal clip policy at this grid resolution. A sharper contrast (smaller κ, finer grid) was not run.
- **Switching instability is not shown for the five-capacity loop.** `alternate_unbounded` is a two-dimensional toy. Alternating between the scalar delay-loop gains studied earlier is stable (spectral radius < 1 for gains in (0, 1)).

## Assumptions and limits

- Every model is scalar and linear, with Gaussian noise. Death means first exit from a fixed band.
- The agent observes its own error exactly. Ultrastability with a noisy essential variable was not tested.
- Regime switches are Poisson and symmetric. The environment does not respond to the agent, except in E2 (depletion) and E1 (shaping, through η).
- Costs are linear in capacity. Real investment returns are rarely linear.
- **Nothing here is fitted to, or validated against, a real system.** "Lean-verified" refers to the difference equations, not to any organism, firm or institution.
