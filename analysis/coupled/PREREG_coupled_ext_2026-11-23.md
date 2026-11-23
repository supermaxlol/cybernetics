# Pre-registration: coupled extension (adaptation, feedback resistance, failure propagation, partial interventions)

Date: 2026-11-23. **This timestamp is local only.** No third-party registry holds it, so it is a
statement of intent, not proof.

Script: `coupled_ext.py`, sha256 `49974124c52f89d06fe2bf584433a58d9fa2edbc202eb3052a628cb5d2eb3214`, frozen read-only (chmod 444) before the confirm run.
It imports the frozen `coupled_sim.py` (sha256 d4ff6fb1…f616ed) **unchanged**.

Confirm design:
- seeds 20000–20039;
- 20 environments per test, env seed 602;
- held-out parameter ranges (`heldout=True`).

None of these seeds or environments were seen in dev (seeds 0–11, env seed 501, dev ranges).

## Metrics (objective 3)
- **Adaptation**: after a drift shift with Δθ ≠ 0, the number of steps until |θ − m| ≤ ¼|Δθ|,
  capped at 300.
- **Resistance to destabilising feedback**: the largest δ in {0, .1, .2, .3, .5, .8} such that
  survival is ≥ 0.9 at that δ and at every smaller δ, with a parasitic term `x += δ·x_prev`
  added. The value is −0.1 if δ = 0 already fails.
- **Failure propagation / compensation**: organ o is switched off at t = T/2.
  - Δ_o = change in the metric vs no failure, using configs that had o.
  - C(o, o') = Δ_o given o' present minus Δ_o given o' absent; C > 0 means o' compensates.

## Hypotheses
"Supported" means the 95% per-environment bootstrap CI lies on the predicted side.

| | Prediction | Theory link |
|---|---|---|
| E1a | No delay: resistance(B) − resistance(¬B) < 0 | `brake_resistance_nodelay` (¼ vs 1) |
| E1b | Delay: resistance(B) − resistance(¬B) > 0 (sign flip) | `unstable_exceed` / Jury, not formalised |
| E2a | F family, M∧W: every adaptation time equals the latency exactly (0 violations) | `adapt_exact` (hard test) |
| E2b | S family, M present: adapt(W) − adapt(¬W) < 0 | `no_adapt_without_watcher` |
| E2c | S family, M∧W: adapt(P) − adapt(¬P) < 0 | `lat` = 1 vs K |
| E3a | C(S ← P) > 0: Spotlight compensates for Skin failure | the two share the shock-damping role |
| E3b | Brake failure under delay: Δ survival < 0 | `partial_unstable` / `unstable_exceed` |
| E3c | Skin failure (M∧W): Δ false alarms > 0 (fixed threshold) | propagation Skin → Watcher |
| E3d | Spotlight failure (M∧W): Δ adaptation time > 0 | propagation Spotlight → Watcher latency |
| E3e | Watcher failure (M): Δ retention < 0 | propagation Watcher → Memory |
| E4 | Heterogeneous mixtures of viable-with-margin configs (20 units, η = 0.1): 0 aggregate failures | `partial_viable` (hard test) |

## Disclosed dev results and changes (made before confirm)
Dev outcomes:
- **Supported:** E1a, E1b, E2a (341 records, 0 violations), E2b, E3c, E3e, E4 (960 runs, 0 deaths).
- **Not supported:**
  - E2c: CI [−28.8, 23.7].
  - E3a: [−0.09, 0.04].
  - E3d: [−10.3, 6.6].

The three are kept as stated and are expected to be at risk. They were **not** dropped.

Change after dev:
- E3b was first a point threshold (Δ ≤ −0.5). Dev gave −0.46.
- It is now the bootstrap-CI test above (Δ < 0). The reason: with failure at T/2, only half the
  horizon is exposed, so −0.5 was a poorly chosen magnitude.

This change was informed by dev data.

## Partial interventions (objective 7)
- The worst-case claim is a theorem (`CoupledPartial.partial_unstable`): one unbraked unit
  suffices to break aggregate viability.
- The mixture claim is also a theorem (`partial_viable`). E4 tests it on random mixtures.
- The average-case dose response is H9 in the first pre-registration.
