import FiveOrgans.CrossScaleTest
import FiveOrgans.RowConcentration

/-!
# A targeted φ test: one block coordinate, two states

The full test (`CrossScaleTest.split_refutes_lumpable` + `RowConcentration.rows_tail`) pays for
a union over all `2^m` subsets and all `m` rows, so it has low power (see
`analysis/REAL_RUN_2026-11-22.md`). If one contrast is fixed in advance, two states `x₁, x₂` in the
same block and one target block `y`, a much smaller error bound suffices.

* `set_tail` — two-sided Hoeffding for the empirical mass of one fixed set `A`:
  `P(|emp(A) − p(A)| ≥ t) ≤ 2 exp(−2 N t²)`.
* `contrast_refutes` — deterministic: if the two true block probabilities are each within `tᵢ` of
  their estimates and the estimates differ by more than `t₁ + t₂`, then **no** macro kernel makes
  `φ` exactly lumpable.

With `tᵢ = √(log(4/α)/(2Nᵢ))` both estimates are within `tᵢ` with probability `≥ 1 − α` (union of
two events of probability `≤ α/2` each). Still assumed (EMP?): each state's successors are `Nᵢ`
i.i.d. draws (time-homogeneous Markov logs, `Nᵢ` fixed). Choosing the contrast after looking at
the same data voids the error rate; it must be fixed before the data it is tested on.
-/

namespace FiveOrgans.CrossScaleContrast
open MeasureTheory ProbabilityTheory Finset Real FiveOrgans.CrossScaleMarkov
  FiveOrgans.CrossScaleTest FiveOrgans.RowConcentration

section Det
variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype Y] in
/-- **A refuting contrast.** -/
theorem contrast_refutes {φ : X → Y} {P Ph : X → X → ℝ} {x₁ x₂ : X} (hφ : φ x₁ = φ x₂) (y : Y)
    {t₁ t₂ : ℝ} (h1 : |blk φ P x₁ y - blk φ Ph x₁ y| ≤ t₁)
    (h2 : |blk φ P x₂ y - blk φ Ph x₂ y| ≤ t₂)
    (hgap : t₁ + t₂ < |blk φ Ph x₁ y - blk φ Ph x₂ y|) : ¬ ∃ Q, Lumpable φ P Q := by
  rintro ⟨Q, hQ⟩
  have e1 : blk φ P x₁ y = Q (φ x₁) y := hQ x₁ y
  have e2 : blk φ P x₂ y = Q (φ x₂) y := hQ x₂ y
  rw [hφ] at e1
  have : |blk φ Ph x₁ y - blk φ Ph x₂ y|
      ≤ |blk φ P x₁ y - blk φ Ph x₁ y| + |blk φ P x₂ y - blk φ Ph x₂ y| := by
    rw [abs_le]
    constructor <;>
    linarith [le_abs_self (blk φ P x₁ y - blk φ Ph x₁ y), neg_abs_le (blk φ P x₁ y - blk φ Ph x₁ y),
      le_abs_self (blk φ P x₂ y - blk φ Ph x₂ y), neg_abs_le (blk φ P x₂ y - blk φ Ph x₂ y)]
  linarith

end Det

section Prob
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- **Two-sided tail for one fixed set:** `P(|emp(A) − p(A)| ≥ t) ≤ 2 exp(−2 N t²)`. -/
theorem set_tail {Z : ℕ → Ω → α} (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z μ)
    {p : α → ℝ} (hlaw : ∀ i a, μ[fun ω => ind {a} (Z i ω)] = p a) (hp1 : ∑ a, p a = 1)
    {N : ℕ} (hN : 0 < N) (A : Finset α) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ a ∈ A, (emp Z N ω a - p a)|} ≤ 2 * exp (-(2 * N * t ^ 2)) := by
  have hc : ∀ ω, ∑ a ∈ Aᶜ, (emp Z N ω a - p a) = -∑ a ∈ A, (emp Z N ω a - p a) := by
    intro ω
    have h0 : ∑ a, (emp Z N ω a - p a) = 0 := by rw [sum_sub_distrib, emp_sum Z hN ω, hp1, sub_self]
    have := sum_add_sum_compl A (fun a => emp Z N ω a - p a)
    linarith
  have hsub : {ω | t ≤ |∑ a ∈ A, (emp Z N ω a - p a)|}
      ⊆ {ω | (2 * t) / 2 ≤ ∑ a ∈ A, (emp Z N ω a - p a)}
        ∪ {ω | (2 * t) / 2 ≤ ∑ a ∈ Aᶜ, (emp Z N ω a - p a)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union, hc] at hω ⊢
    rcases le_abs'.1 hω with h | h
    · right; linarith
    · left; linarith
  have t1 := subset_tail hZ hind hlaw hN A (by linarith : (0 : ℝ) ≤ 2 * t)
  have t2 := subset_tail hZ hind hlaw hN Aᶜ (by linarith : (0 : ℝ) ≤ 2 * t)
  have he : -((N : ℝ) * (2 * t) ^ 2) / 2 = -(2 * N * t ^ 2) := by ring
  rw [he] at t1 t2
  calc μ.real {ω | t ≤ |∑ a ∈ A, (emp Z N ω a - p a)|}
      ≤ μ.real ({ω | (2 * t) / 2 ≤ ∑ a ∈ A, (emp Z N ω a - p a)}
        ∪ {ω | (2 * t) / 2 ≤ ∑ a ∈ Aᶜ, (emp Z N ω a - p a)}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ 2 * exp (-(2 * N * t ^ 2)) := by linarith

/-- The runner's `t = √(log(4/α)/(2N))` makes each two-sided tail exactly `α/2`. -/
theorem t_solves {N : ℕ} (hN : 0 < N) {a : ℝ} (ha : 0 < a) {t : ℝ}
    (ht : t ^ 2 = log (4 / a) / (2 * N)) : 2 * exp (-(2 * N * t ^ 2)) = a / 2 := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have : -(2 * (N : ℝ) * t ^ 2) = -log (4 / a) := by rw [ht]; field_simp
  rw [this, exp_neg, exp_log (by positivity)]
  field_simp
  ring

end Prob

end FiveOrgans.CrossScaleContrast
