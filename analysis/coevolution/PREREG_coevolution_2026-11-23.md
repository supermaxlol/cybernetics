# Pre-registration: co-evolution (endogenous recursive viability)

Date: 2026-11-23. **The timestamp is local only.** The scripts and this file were frozen with `chmod 444`, and their SHA-256 hashes were written to `FROZEN_coevolution.sha256` before `coevo_sim.py confirm` ran. No third party timestamped them.

The formal base is `FiveOrgans/CoupledEndogenous.lean`, which proves:

- the rate threshold `rate_iff`: a policy exists iff `v ≤ r + η·X`;
- depletion: `depletion_kills` and `static_not_recursive`;
- reconfiguration: `alternate_unbounded` and `dwell_two_safe`;
- the cost of keeping up: `response_lower`, `afford_impossible` and `accel_impossible`.

The simulation tests what the theorems do not cover: noise, non-optimal policies, how far the deterministic predictions hold up quantitatively, and adaptive reconfiguration (ultrastability).

All thresholds below were set **after** the dev run (seeds 0–99, `coevo_dev_raw.json`), in which every hypothesis passed. The confirm run uses fresh noise keys (base 200) and 200 seeds per cell. It also adds cells outside the dev range:

- E1 at tolerance X = 6;
- E2 at consumption c = 0.2;
- E3 at acceleration a = 2·10⁻⁴.

No threshold changes after confirm starts.

| ID | Prediction | Pass rule |
|---|---|---|
| C1 | Implementation of `rate_iff`: with no noise, the clipped policy survives iff v ≤ r + ηX | 0 mismatching cells |
| C2 | Noise lowers the survivable drift. The boundary (the largest v/(r + ηX) with survival ≥ 0.5) does not increase with noise s and is < 1 for s ≥ 0.15 | every (X, η, r, policy) family |
| C3 | Niche construction helps under noise: the survivable absolute drift v* at s = 0.3 does not decrease with η, and v*(η = 0.15) > v*(η = 0) | every (X, r, policy) |
| C4 | Depletion: every β > 0 cell dies, including cells that are statically viable (q₀ ≥ c). Mean time to death is within 5% of the closed-form t* when regeneration noise is present. With β = 0 and q₀ > c, survival is ≥ 0.95 | all three |
| C5 | Cost of viability: in an accelerating environment, mean time to death is maximised at an *interior* investment rate b. The lowest b dies of drift (no budget deaths) and the highest b dies of budget | every (a, s) |
| C5b | `accel_impossible`: every E3 cell dies within T = 20000 | all cells |
| C6 | The deterministic recursion predicts the mean time to death under noise s = 0.05 within 10% | all s = 0.05 cells |
| C7 | Ultrastability: when regimes alternate between "the Brake is required" (delay) and "the Brake is fatal" (destabilising feedback), the Ashby agent with no refractory period (m_d = 1) beats both fixed configurations in every cell, by ≥ 0.3 on average | both parts |
| C8 | A refractory period after switching (m_d = 5) costs survival: mean change < −0.1 | — |
| C9 | The regime-aware oracle does at least as well as the ultrastable agent in every cell | — |
| C10 | Chattering: the number of switches falls as the switching threshold τ rises (m_d = 1) | Spearman < 0, p < 0.05 |

## Limits stated in advance

- **Scalar and linear models only:** E1–E3 are scalar error recursions, and E4 is the delay loop from `Coupled.lean` plus a feedback-regime switch. Nothing here models a specific real system.
- **C1, C4's closed form and C5b check the theorems:** they test the implementation and the theorems' reach under noise; they are not independent discoveries.
- **The switching counterexample (`alternate_unbounded`) is a two-dimensional toy.** Switching between the scalar delay-loop Brake gains studied earlier does *not* destabilise: for gains in (0, 1), every alternating product has spectral radius < 1. The toy shows that reconfiguration *can* destroy viability. It does not show that this happens in the five-capacity loop.
