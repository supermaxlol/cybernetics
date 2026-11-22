import FiveOrgans.PoissonConf

/-!
# Both orientations: KL tests for means near 0 OR near 1

The KL exponent is sharp when the mean is near 0. For a mean near 1 (for example
`P(next = H | H) ≈ 0.75`), apply it to `1 − X`, whose mean `1 − p` is small. Picking the
orientation after seeing the data is a choice made with the data, so the rule below fires if
EITHER orientation rejects, and pays for both.

* `flip_measurable`, `flip_indep`, `flip_range`, `flip_mean` — `1 − X` satisfies the same
  hypotheses, with mean `1 − p`.
* `kl_two_sample_flip` — two samples with the same mean `p ∈ (0,1)` (any dependence between
  them): "no `q > 0` in both KL sets for `X`, OR no `q > 0` in both KL sets for `1 − X`" has
  probability `≤ 8 e^{−L}`.
* `kl_two_sample_flip_alpha` — `L = log (8/α)` gives false rejection `≤ α`.

Fixed counts (the random-count union of `PoissonRandom` applies the same way).
-/

namespace FiveOrgans.PoissonFlip
open MeasureTheory ProbabilityTheory Finset Real
open FiveOrgans.PoissonTail FiveOrgans.PoissonConf

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem flip_measurable {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (i : ℕ) :
    Measurable (fun ω => 1 - X i ω) := measurable_const.sub (hX i)

omit [IsProbabilityMeasure μ] in
theorem flip_indep {X : ℕ → Ω → ℝ} (hind : iIndepFun X μ) :
    iIndepFun (fun i ω => 1 - X i ω) μ :=
  hind.comp (fun _ x => 1 - x) (fun _ => measurable_const.sub measurable_id)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
theorem flip_range {X : ℕ → Ω → ℝ} (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) (i : ℕ) (ω : Ω) :
    1 - X i ω ∈ Set.Icc (0 : ℝ) 1 := by
  have := hr i ω; constructor <;> linarith [this.1, this.2]

theorem flip_mean {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (i : ℕ) :
    μ[fun ω => 1 - X i ω] = 1 - p := by
  have hXi : Integrable (X i) μ :=
    Integrable.of_bound (C := 1) (hX i).aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hr i ω).1]; exact (hr i ω).2)
  rw [integral_sub (integrable_const 1) hXi, hm i]; simp

/-- **Two-sample KL test, both orientations.** -/
theorem kl_two_sample_flip {X₁ X₂ : ℕ → Ω → ℝ} (hX₁ : ∀ i, Measurable (X₁ i))
    (hX₂ : ∀ i, Measurable (X₂ i)) (hind₁ : iIndepFun X₁ μ) (hind₂ : iIndepFun X₂ μ)
    (hr₁ : ∀ i ω, X₁ i ω ∈ Set.Icc (0 : ℝ) 1) (hr₂ : ∀ i ω, X₂ i ω ∈ Set.Icc (0 : ℝ) 1)
    {p : ℝ} (hm₁ : ∀ i, μ[X₁ i] = p) (hm₂ : ∀ i, μ[X₂ i] = p) {N₁ N₂ : ℕ} (hN₁ : 0 < N₁)
    (hN₂ : 0 < N₂) (hp : 0 < p) (hp1 : p < 1) (L : ℝ) :
    μ.real ({ω | ∀ q, 0 < q → L ≤ N₁ * poisKL ((∑ i ∈ range N₁, X₁ i ω) / N₁) q ∨
                               L ≤ N₂ * poisKL ((∑ i ∈ range N₂, X₂ i ω) / N₂) q} ∪
            {ω | ∀ q, 0 < q → L ≤ N₁ * poisKL ((∑ i ∈ range N₁, (1 - X₁ i ω)) / N₁) q ∨
                               L ≤ N₂ * poisKL ((∑ i ∈ range N₂, (1 - X₂ i ω)) / N₂) q})
      ≤ 8 * exp (-L) := by
  calc _ ≤ _ + _ := measureReal_union_le _ _
    _ ≤ 4 * exp (-L) + 4 * exp (-L) := add_le_add
          (kl_two_sample hX₁ hX₂ hind₁ hind₂ hr₁ hr₂ hm₁ hm₂ hN₁ hN₂ hp L)
          (kl_two_sample (flip_measurable hX₁) (flip_measurable hX₂) (flip_indep hind₁)
            (flip_indep hind₂) (flip_range hr₁) (flip_range hr₂) (flip_mean hX₁ hr₁ hm₁)
            (flip_mean hX₂ hr₂ hm₂) hN₁ hN₂ (by linarith) L)
    _ = 8 * exp (-L) := by ring

/-- **Calibrated, both orientations:** `L = log (8/α)`. -/
theorem kl_two_sample_flip_alpha {X₁ X₂ : ℕ → Ω → ℝ} (hX₁ : ∀ i, Measurable (X₁ i))
    (hX₂ : ∀ i, Measurable (X₂ i)) (hind₁ : iIndepFun X₁ μ) (hind₂ : iIndepFun X₂ μ)
    (hr₁ : ∀ i ω, X₁ i ω ∈ Set.Icc (0 : ℝ) 1) (hr₂ : ∀ i ω, X₂ i ω ∈ Set.Icc (0 : ℝ) 1)
    {p : ℝ} (hm₁ : ∀ i, μ[X₁ i] = p) (hm₂ : ∀ i, μ[X₂ i] = p) {N₁ N₂ : ℕ} (hN₁ : 0 < N₁)
    (hN₂ : 0 < N₂) (hp : 0 < p) (hp1 : p < 1) {α : ℝ} (hα : 0 < α) :
    μ.real ({ω | ∀ q, 0 < q → log (8 / α) ≤ N₁ * poisKL ((∑ i ∈ range N₁, X₁ i ω) / N₁) q ∨
                               log (8 / α) ≤ N₂ * poisKL ((∑ i ∈ range N₂, X₂ i ω) / N₂) q} ∪
            {ω | ∀ q, 0 < q → log (8 / α) ≤ N₁ * poisKL ((∑ i ∈ range N₁, (1 - X₁ i ω)) / N₁) q ∨
                               log (8 / α) ≤ N₂ * poisKL ((∑ i ∈ range N₂, (1 - X₂ i ω)) / N₂) q})
      ≤ α := by
  refine (kl_two_sample_flip hX₁ hX₂ hind₁ hind₂ hr₁ hr₂ hm₁ hm₂ hN₁ hN₂ hp hp1 _).trans_eq ?_
  rw [exp_neg_log (by positivity)]; field_simp

end FiveOrgans.PoissonFlip
