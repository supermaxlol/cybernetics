import FiveOrgans.CrossScale
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Approximate cross-scale maps: verdicts with margin transfer, edge verdicts do not

`CrossScale` needs exact commutation `φ ∘ f = g ∘ φ`. A real system matches a model only up to
an error: `dist (φ (f x)) (g (φ x)) ≤ η` for every micro state `x`. Here `Y` is a metric space.

* `approx_iterate` — if the macro dynamics `g` is `L`-Lipschitz, the mismatch after `n` steps is
  at most `η · Σ_{i<n} L^i`.
* `approx_uniform` — if `L < 1` (the macro model is contracting), the mismatch is at most
  `η / (1 - L)` at every horizon.
* `robust_stay` / `robust_leave` — a macro verdict that holds **with margin** `r ≥ η/(1-L)`
  (the whole closed ball of radius `r` around the macro state lies in `K`, or in its complement)
  holds for the micro system too, at every step. `robust_ablation` applies this to an
  approximately implemented intervention: a margin-robust "ablation kills" verdict transfers.
* `edge_flip` — the margin is needed: with **any** `η > 0` there are systems where the macro
  stays in `K` forever (on its edge) and the micro system leaves `K` at step 1.

Reading: an approximate φ licenses only verdicts that are robust by more than the accumulated
mismatch. Ablation claims about real systems should be made only when the model's verdict has
slack. Scope: deterministic, uniform error bound, contracting macro dynamics. Non-contracting
macro dynamics give the finite-horizon bound only, and that is sharp (`CrossScaleLongRun`).
Stochastic φ: `CrossScaleHazard` (hazard level) and `CrossScaleMarkov` (state level).
-/

namespace FiveOrgans.CrossScaleApprox
open Finset Metric

variable {X Y : Type*} [PseudoMetricSpace Y]

/-- Accumulated mismatch after `n` steps. -/
theorem approx_iterate {f : X → X} {g : Y → Y} {φ : X → Y} {η L : ℝ}
    (hf : ∀ x, dist (φ (f x)) (g (φ x)) ≤ η) (hg : ∀ y y', dist (g y) (g y') ≤ L * dist y y')
    (hL : 0 ≤ L) (x : X) (n : ℕ) :
    dist (φ (f^[n] x)) (g^[n] (φ x)) ≤ η * ∑ i ∈ range n, L ^ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hsum : η * ∑ i ∈ range (n + 1), L ^ i = η + L * (η * ∑ i ∈ range n, L ^ i) := by
      rw [sum_range_succ', mul_add, mul_sum, mul_sum, mul_sum]
      simp only [pow_succ, pow_zero, mul_one]
      rw [add_comm]; congr 1
      exact sum_congr rfl fun i _ => by ring
    rw [hsum]
    calc dist (φ (f (f^[n] x))) (g (g^[n] (φ x)))
        ≤ dist (φ (f (f^[n] x))) (g (φ (f^[n] x))) + dist (g (φ (f^[n] x))) (g (g^[n] (φ x))) :=
          dist_triangle _ _ _
      _ ≤ η + L * (η * ∑ i ∈ range n, L ^ i) :=
          add_le_add (hf _) ((hg _ _).trans (mul_le_mul_of_nonneg_left ih hL))

/-- Geometric partial sums are bounded by `1/(1-L)` for `0 ≤ L < 1`. -/
theorem geom_le {L : ℝ} (hL : 0 ≤ L) (hL1 : L < 1) (n : ℕ) :
    ∑ i ∈ range n, L ^ i ≤ 1 / (1 - L) := by
  have hpos : 0 < 1 - L := by linarith
  induction n with
  | zero => rw [sum_range_zero]; positivity
  | succ n ih =>
    have hs : ∑ i ∈ range (n + 1), L ^ i = 1 + L * ∑ i ∈ range n, L ^ i := by
      rw [sum_range_succ', mul_sum, add_comm]
      simp only [pow_zero]
      congr 1
      exact sum_congr rfl fun i _ => by ring
    rw [hs]
    have : L * ∑ i ∈ range n, L ^ i ≤ L * (1 / (1 - L)) := mul_le_mul_of_nonneg_left ih hL
    have h1 : 1 + L * (1 / (1 - L)) = 1 / (1 - L) := by field_simp; ring
    linarith

/-- **Uniform mismatch bound for a contracting macro model.** -/
theorem approx_uniform {f : X → X} {g : Y → Y} {φ : X → Y} {η L : ℝ} (hη : 0 ≤ η)
    (hf : ∀ x, dist (φ (f x)) (g (φ x)) ≤ η) (hg : ∀ y y', dist (g y) (g y') ≤ L * dist y y')
    (hL : 0 ≤ L) (hL1 : L < 1) (x : X) (n : ℕ) :
    dist (φ (f^[n] x)) (g^[n] (φ x)) ≤ η / (1 - L) :=
  (approx_iterate hf hg hL x n).trans (by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left (geom_le hL hL1 n) hη)

/-- **Staying viable with margin transfers.** -/
theorem robust_stay {f : X → X} {g : Y → Y} {φ : X → Y} {η L r : ℝ} (hη : 0 ≤ η)
    (hf : ∀ x, dist (φ (f x)) (g (φ x)) ≤ η) (hg : ∀ y y', dist (g y) (g y') ≤ L * dist y y')
    (hL : 0 ≤ L) (hL1 : L < 1) (hr : η / (1 - L) ≤ r) {K : Set Y} (x : X)
    (hK : ∀ n, closedBall (g^[n] (φ x)) r ⊆ K) (n : ℕ) : φ (f^[n] x) ∈ K :=
  hK n (mem_closedBall.2 ((approx_uniform hη hf hg hL hL1 x n).trans hr))

/-- **Leaving with margin transfers.** -/
theorem robust_leave {f : X → X} {g : Y → Y} {φ : X → Y} {η L r : ℝ} (hη : 0 ≤ η)
    (hf : ∀ x, dist (φ (f x)) (g (φ x)) ≤ η) (hg : ∀ y y', dist (g y) (g y') ≤ L * dist y y')
    (hL : 0 ≤ L) (hL1 : L < 1) (hr : η / (1 - L) ≤ r) {K : Set Y} (x : X) (n : ℕ)
    (hK : closedBall (g^[n] (φ x)) r ⊆ Kᶜ) : φ (f^[n] x) ∉ K :=
  hK (mem_closedBall.2 ((approx_uniform hη hf hg hL hL1 x n).trans hr))

open FiveOrgans.CrossScale in
/-- **Approximate implementation of an ablation:** if the ablated dynamics match up to `η`
and the macro ablation leaves `K` with margin `r ≥ η/(1-L)`, the micro ablation leaves too. -/
theorem robust_ablation {I : Type*} {m : Sys X I} {M : Sys Y I} {φ : X → Y} {η L r : ℝ}
    (i : I) (hη : 0 ≤ η) (hf : ∀ x, dist (φ (m.abl i x)) (M.abl i (φ x)) ≤ η)
    (hg : ∀ y y', dist (M.abl i y) (M.abl i y') ≤ L * dist y y') (hL : 0 ≤ L) (hL1 : L < 1)
    (hr : η / (1 - L) ≤ r) {K : Set Y} (x : X) (n : ℕ)
    (hK : closedBall ((M.abl i)^[n] (φ x)) r ⊆ Kᶜ) : (m.abl i)^[n] x ∉ φ ⁻¹' K :=
  robust_leave hη hf hg hL hL1 hr x n hK

/-- **The margin is needed:** for every `η > 0`, micro `f ≡ η`, macro `g ≡ 0` (so `L = 0`),
`φ = id` on `ℝ`, `K = (-∞, 0]`. The mismatch is `η`; the macro stays in `K` forever from 0
(on the edge), while the micro leaves `K` at step 1. -/
theorem edge_flip {η : ℝ} (hη : 0 < η) :
    (∀ x : ℝ, dist ((fun _ : ℝ => η) x) ((fun _ : ℝ => (0 : ℝ)) x) ≤ η) ∧
    (∀ n, (fun _ : ℝ => (0 : ℝ))^[n] 0 ∈ Set.Iic (0 : ℝ)) ∧
    (fun _ : ℝ => η)^[1] 0 ∉ Set.Iic (0 : ℝ) := by
  refine ⟨fun _ => by simp [abs_of_pos hη], fun n => ?_, by simp; linarith⟩
  cases n with
  | zero => simp
  | succ n => rw [Function.iterate_succ_apply']; simp

end FiveOrgans.CrossScaleApprox
