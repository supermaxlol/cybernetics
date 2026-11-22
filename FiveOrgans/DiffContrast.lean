import FiveOrgans.CrossScaleContrast

/-!
# A sharper contrast test: Hoeffding on the difference

`CrossScaleContrast` bounds each of the two estimates separately and adds the radii. Bounding the
difference `D̂ = p̂₁ − p̂₂` directly is about `√2` sharper and needs no knowledge of the common
probability under the null.

* `weighted_tail` — weighted Hoeffding: for independent `W i ∈ [0,1]`,
  `P(ε ≤ Σ wᵢ (Wᵢ − E Wᵢ)) ≤ exp(−2ε² / Σ wᵢ²)`.
* `weighted_abs_tail` — two-sided, factor 2.
* `wt N₁ N₂` — weights `+1/N₁` on the first `N₁` draws, `−1/N₂` on the next `N₂`;
  `wt_sq_sum` gives `Σ wt² = 1/N₁ + 1/N₂`; `wt_centered` gives `Σ wt (W − E W) = D̂ − (p₁ − p₂)`.
* `diff_tail` — `P(t ≤ |D̂ − (p₁ − p₂)|) ≤ 2 exp(−2t² / (1/N₁ + 1/N₂))`.
* `diff_t_solves` — `t² = (1/N₁ + 1/N₂) log(2/a) / 2` makes that bound exactly `a`.
* `diff_refutes` — deterministic: if `|D̂ − (true difference)| ≤ t < |D̂|` for two states in the
  same block, `φ` is not exactly lumpable.

Still assumed (EMP?): the draws are independent with the stated means (each micro state's
successors are i.i.d., `Nᵢ` treated as fixed); the contrast is fixed before the data.
-/

namespace FiveOrgans.DiffContrast
open MeasureTheory ProbabilityTheory Finset Real FiveOrgans.CrossScaleMarkov
  FiveOrgans.CrossScaleTest
open scoped NNReal

section Prob
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Weighted Hoeffding.** -/
theorem weighted_tail {W : ℕ → Ω → ℝ} (hW : ∀ i, Measurable (W i)) (hind : iIndepFun W μ)
    (h01 : ∀ i ω, W i ω ∈ Set.Icc (0 : ℝ) 1) (w : ℕ → ℝ) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hw : 0 < ∑ i ∈ range n, w i ^ 2) :
    μ.real {ω | ε ≤ ∑ i ∈ range n, w i * (W i ω - μ[W i])}
      ≤ exp (-(2 * ε ^ 2) / ∑ i ∈ range n, w i ^ 2) := by
  set X : ℕ → Ω → ℝ := fun i ω => w i * (W i ω - μ[W i]) with hX
  have hindX : iIndepFun X μ := by
    have := hind.comp (fun i (x : ℝ) => w i * (x - ∫ y, W i y ∂μ)) (fun i => by fun_prop)
    exact this
  set c : ℕ → ℝ≥0 := fun i =>
    @HMul.hMul ℝ≥0 ℝ≥0 ℝ≥0 _ ⟨w i ^ 2, sq_nonneg (w i)⟩ ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) with hcdef
  have hsub : ∀ i ∈ range n, HasSubgaussianMGF (X i) (c i) μ := fun i _ =>
    (hasSubgaussianMGF_of_mem_Icc (hW i).aemeasurable (ae_of_all _ (h01 i))).const_mul (w i)
  have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindX hsub hε
  have hc : ∀ i, ((c i : ℝ≥0) : ℝ) = w i ^ 2 / 4 := by
    intro i
    show w i ^ 2 * (((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = w i ^ 2 / 4
    push_cast
    simp
    ring
  rw [NNReal.coe_sum, sum_congr rfl (fun i _ => hc i), ← sum_div] at hH
  convert hH using 2
  have := hw.ne'
  field_simp
  ring

/-- Two-sided weighted Hoeffding. -/
theorem weighted_abs_tail {W : ℕ → Ω → ℝ} (hW : ∀ i, Measurable (W i)) (hind : iIndepFun W μ)
    (h01 : ∀ i ω, W i ω ∈ Set.Icc (0 : ℝ) 1) (w : ℕ → ℝ) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hw : 0 < ∑ i ∈ range n, w i ^ 2) :
    μ.real {ω | ε ≤ |∑ i ∈ range n, w i * (W i ω - μ[W i])|}
      ≤ 2 * exp (-(2 * ε ^ 2) / ∑ i ∈ range n, w i ^ 2) := by
  have hw' : ∑ i ∈ range n, (-w i) ^ 2 = ∑ i ∈ range n, w i ^ 2 :=
    sum_congr rfl fun i _ => by ring
  have t1 := weighted_tail (μ := μ) hW hind h01 w n hε hw
  have t2 := weighted_tail (μ := μ) hW hind h01 (fun i => -w i) n hε (hw' ▸ hw)
  rw [hw'] at t2
  have hsub : {ω | ε ≤ |∑ i ∈ range n, w i * (W i ω - μ[W i])|}
      ⊆ {ω | ε ≤ ∑ i ∈ range n, w i * (W i ω - μ[W i])}
        ∪ {ω | ε ≤ ∑ i ∈ range n, -w i * (W i ω - μ[W i])} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    have hneg : ∑ i ∈ range n, -w i * (W i ω - μ[W i])
        = -∑ i ∈ range n, w i * (W i ω - μ[W i]) := by
      rw [← sum_neg_distrib]; exact sum_congr rfl fun i _ => by ring
    rw [hneg]
    rcases le_abs'.1 hω with h | h
    · right; linarith
    · left; linarith
  calc _ ≤ μ.real ({ω | ε ≤ ∑ i ∈ range n, w i * (W i ω - μ[W i])}
        ∪ {ω | ε ≤ ∑ i ∈ range n, -w i * (W i ω - μ[W i])}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- Contrast weights: `+1/N₁` on the first `N₁` draws, `−1/N₂` afterwards. -/
noncomputable def wt (N₁ N₂ : ℕ) (i : ℕ) : ℝ := if i < N₁ then 1 / N₁ else -(1 / N₂)

theorem wt_sq_sum {N₁ N₂ : ℕ} (h1 : 0 < N₁) (h2 : 0 < N₂) :
    ∑ i ∈ range (N₁ + N₂), wt N₁ N₂ i ^ 2 = 1 / N₁ + 1 / N₂ := by
  rw [sum_range_add]
  have a : ∑ i ∈ range N₁, wt N₁ N₂ i ^ 2 = ∑ _i ∈ range N₁, (1 / (N₁ : ℝ)) ^ 2 :=
    sum_congr rfl fun i hi => by simp [wt, mem_range.1 hi]
  have b : ∑ i ∈ range N₂, wt N₁ N₂ (N₁ + i) ^ 2 = ∑ _i ∈ range N₂, (1 / (N₂ : ℝ)) ^ 2 :=
    sum_congr rfl fun i _ => by simp [wt]
  rw [a, b, sum_const, sum_const, card_range, card_range, nsmul_eq_mul, nsmul_eq_mul]
  have : (N₁ : ℝ) ≠ 0 := by positivity
  have : (N₂ : ℝ) ≠ 0 := by positivity
  field_simp

omit [IsProbabilityMeasure μ] in
/-- The weighted centred sum is the estimated contrast minus the true one. -/
theorem wt_centered {N₁ N₂ : ℕ} (W : ℕ → Ω → ℝ) {p₁ p₂ : ℝ}
    (hm1 : ∀ i < N₁, μ[W i] = p₁) (hm2 : ∀ i, μ[W (N₁ + i)] = p₂) (ω : Ω) :
    ∑ i ∈ range (N₁ + N₂), wt N₁ N₂ i * (W i ω - μ[W i])
      = ((1 / N₁) * ∑ i ∈ range N₁, W i ω - (1 / N₂) * ∑ i ∈ range N₂, W (N₁ + i) ω)
        - ((1 / N₁) * ∑ _i ∈ range N₁, p₁ - (1 / N₂) * ∑ _i ∈ range N₂, p₂) := by
  rw [sum_range_add]
  have a : ∑ i ∈ range N₁, wt N₁ N₂ i * (W i ω - μ[W i])
      = ∑ i ∈ range N₁, (1 / (N₁ : ℝ)) * (W i ω - p₁) :=
    sum_congr rfl fun i hi => by simp [wt, mem_range.1 hi, hm1 i (mem_range.1 hi)]
  have b : ∑ i ∈ range N₂, wt N₁ N₂ (N₁ + i) * (W (N₁ + i) ω - μ[W (N₁ + i)])
      = ∑ i ∈ range N₂, (-(1 / (N₂ : ℝ))) * (W (N₁ + i) ω - p₂) :=
    sum_congr rfl fun i _ => by simp [wt, hm2 i]
  rw [a, b, ← mul_sum, ← mul_sum, sum_sub_distrib, sum_sub_distrib]
  ring

/-- **The difference test's tail:** `P(t ≤ |D̂ − (p₁ − p₂)|) ≤ 2 exp(−2t² / (1/N₁ + 1/N₂))`. -/
theorem diff_tail {W : ℕ → Ω → ℝ} (hW : ∀ i, Measurable (W i)) (hind : iIndepFun W μ)
    (h01 : ∀ i ω, W i ω ∈ Set.Icc (0 : ℝ) 1) {N₁ N₂ : ℕ} (h1 : 0 < N₁) (h2 : 0 < N₂)
    {p₁ p₂ : ℝ} (hm1 : ∀ i < N₁, μ[W i] = p₁) (hm2 : ∀ i, μ[W (N₁ + i)] = p₂)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |((1 / N₁) * ∑ i ∈ range N₁, W i ω - (1 / N₂) * ∑ i ∈ range N₂, W (N₁ + i) ω)
        - (p₁ - p₂)|} ≤ 2 * exp (-(2 * t ^ 2) / (1 / N₁ + 1 / N₂)) := by
  have hs := wt_sq_sum (N₂ := N₂) h1 h2
  have hpos : 0 < ∑ i ∈ range (N₁ + N₂), wt N₁ N₂ i ^ 2 := by rw [hs]; positivity
  have h := weighted_abs_tail (μ := μ) hW hind h01 (wt N₁ N₂) (N₁ + N₂) ht hpos
  rw [hs] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, wt_centered (μ := μ) W hm1 hm2 ω, sum_const, card_range,
    nsmul_eq_mul]
  have : (N₁ : ℝ) ≠ 0 := by positivity
  have : (N₂ : ℝ) ≠ 0 := by positivity
  field_simp

/-- The runner's radius `t² = s · log(2/a) / 2` (with `s = 1/N₁ + 1/N₂`) makes the tail exactly `a`. -/
theorem diff_t_solves {s a t : ℝ} (hs : 0 < s) (ha : 0 < a) (ht : t ^ 2 = s * log (2 / a) / 2) :
    2 * exp (-(2 * t ^ 2) / s) = a := by
  have : -(2 * t ^ 2) / s = -log (2 / a) := by rw [ht]; field_simp
  rw [this, exp_neg, exp_log (by positivity)]
  field_simp

end Prob

section Det
variable {X Y : Type*} [Fintype X]

/-- **A refuting difference.** -/
theorem diff_refutes {φ : X → Y} {P : X → X → ℝ} {x₁ x₂ : X} (hφ : φ x₁ = φ x₂) (y : Y)
    {D t : ℝ} (hD : |D - (blk φ P x₁ y - blk φ P x₂ y)| ≤ t) (hgap : t < |D|) :
    ¬ ∃ Q, Lumpable φ P Q := by
  rintro ⟨Q, hQ⟩
  have e1 : blk φ P x₁ y = Q (φ x₁) y := hQ x₁ y
  have e2 : blk φ P x₂ y = Q (φ x₂) y := hQ x₂ y
  rw [e1, e2, hφ, sub_self, sub_zero] at hD
  linarith

end Det

end FiveOrgans.DiffContrast
