import FiveOrgans.CrossScaleApprox
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Non-contracting macro models: no long-run transfer from a per-step bound

`CrossScaleApprox` gives a uniform drift bound `η/(1−L)` when the macro model contracts
(`L < 1`). For `L ≥ 1` only the finite-horizon bound `η Σ L^i` was proved. This module shows
that this is the best possible: with `L = 1` no uniform bound exists.

* `drift_unbounded` — micro `x ↦ x + η`, macro `id` (an isometry, `L = 1`), `φ = id` on `ℝ`.
  The per-step mismatch is exactly `η`, but after `n` steps the gap is `n η`.
* `longrun_flip` — so for every `η > 0` and every margin `R`, the macro stays in `(-∞, 0]`
  forever (with margin `R` around its trajectory... it never moves), while the micro leaves
  `(-∞, R]` at some step. **No margin, however large, licenses a lifetime verdict for a
  non-contracting model with a uniform per-step error.**

Reading: for non-contracting macro models, lifetime verdicts need a summable mismatch (as in
`CrossScaleHazard`) or contraction. A small, constant per-step error is not enough.
-/

namespace FiveOrgans.CrossScaleLongRun

theorem drift_unbounded (η : ℝ) (n : ℕ) : (fun x : ℝ => x + η)^[n] 0 = n * η := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih]; push_cast; ring

/-- **Lifetime verdicts flip for a non-contracting model, whatever the margin.** -/
theorem longrun_flip {η : ℝ} (hη : 0 < η) (R : ℝ) :
    (∀ x : ℝ, dist (x + η) (id x) ≤ η) ∧
    (∀ y y' : ℝ, dist (id y) (id y') ≤ 1 * dist y y') ∧
    (∀ n, (id : ℝ → ℝ)^[n] 0 = 0) ∧
    ∃ n, R < (fun x : ℝ => x + η)^[n] 0 := by
  refine ⟨fun x => by simp [Real.dist_eq, abs_of_pos hη], fun y y' => by simp, fun n => by simp, ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (R / η)
  refine ⟨n, ?_⟩
  rw [drift_unbounded]
  have := (div_lt_iff₀ hη).1 hn
  linarith

end FiveOrgans.CrossScaleLongRun
