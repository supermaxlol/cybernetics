import FiveOrgans.Ville

/-!
# A two-arm anytime-valid test (paired design)

Two arms give draws `X i, Y i ∈ [0,1]` at each step `i`. The pairs `(X i, Y i)` are independent
across `i`, and the two arms may be dependent within a pair. The null is **no arm effect at any
step**: `E X i = E Y i` for all `i` (the common mean may drift with `i`).

The paired difference `D i = (X i − Y i + 1)/2` lies in `[0,1]` and has mean `1/2` under the
null. So `Ville.ville_bern_grid` with `p = 1/2` gives a test valid for every sample size at once.
- `ville_two_arm`: crossing probability `≤ |Λ| e^{−A}` over all `m ≤ T` and tilts in `Λ`.
- `ville_two_arm_alpha`: with `A = log(|Λ|/α)` the false-alarm probability is `≤ α`.
  Use `Λ = {l, −l}` for a two-sided test.

Scope.
- Paired design: both arms are observed at every step.
- An unpaired design (random visit counts per arm) is not covered.
- Nothing here is about real data.
-/

namespace FiveOrgans.VilleTwoArm
open MeasureTheory ProbabilityTheory Finset Real FiveOrgans.Ville

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Paired difference mapped into `[0,1]`. -/
noncomputable def dif (X Y : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) : ℝ := (X i ω - Y i ω + 1) / 2

omit mΩ [IsProbabilityMeasure μ] in
theorem dif_mem {X Y : ℕ → Ω → ℝ} (hXr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hYr : ∀ i ω, Y i ω ∈ Set.Icc (0 : ℝ) 1) (i : ℕ) (ω : Ω) :
    dif X Y i ω ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨a, b⟩ := hXr i ω
  obtain ⟨c, d⟩ := hYr i ω
  unfold dif
  constructor
  · apply div_nonneg <;> linarith
  · rw [div_le_one (by norm_num)]; linarith

omit [IsProbabilityMeasure μ] in
theorem dif_meas {X Y : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (i : ℕ) : Measurable (dif X Y i) :=
  (((hX i).sub (hY i)).add_const 1).div_const 2

theorem int_unit {Y : Ω → ℝ} (hY : Measurable Y) (hr : ∀ ω, Y ω ∈ Set.Icc (0 : ℝ) 1) :
    Integrable Y μ :=
  Integrable.of_bound (C := 1) hY.aestronglyMeasurable (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hr ω).1]; exact (hr ω).2)

theorem dif_mean {X Y : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) (hYr : ∀ i ω, Y i ω ∈ Set.Icc (0 : ℝ) 1)
    {i : ℕ} (hm : μ[X i] = μ[Y i]) : μ[dif X Y i] = 1 / 2 := by
  have iX := int_unit (μ := μ) (hX i) (hXr i)
  have iY := int_unit (μ := μ) (hY i) (hYr i)
  unfold dif
  have iD : Integrable (fun a => X i a - Y i a) μ := iX.sub iY
  rw [integral_div, integral_add iD (integrable_const 1), integral_sub iX iY, hm]
  simp

omit [IsProbabilityMeasure μ] in
theorem dif_indep {X Y : ℕ → Ω → ℝ} (hind : iIndepFun (fun i ω => (X i ω, Y i ω)) μ) :
    iIndepFun (dif X Y) μ :=
  hind.comp (fun _ q => (q.1 - q.2 + 1) / 2) (fun _ => by fun_prop)

/-- **Two-arm Ville bound.** Under no arm effect, the paired tilted statistic crosses `A` for
some tilt in `Λ` and some `m ≤ T` with probability `≤ |Λ| e^{−A}`. -/
theorem ville_two_arm {X Y : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (hXr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hYr : ∀ i ω, Y i ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun (fun i ω => (X i ω, Y i ω)) μ) (hm : ∀ i, μ[X i] = μ[Y i])
    (Λ : Finset ℝ) (A : ℝ) (T : ℕ) :
    μ.real {ω | ∃ l ∈ Λ, ∃ m ∈ Icc 1 T,
        A ≤ l * ∑ i ∈ range m, dif X Y i ω - m * log (1 + 1 / 2 * (exp l - 1))}
      ≤ Λ.card * exp (-A) :=
  ville_bern_grid (dif_meas hX hY) (dif_mem hXr hYr) (dif_indep hind)
    (fun i => dif_mean hX hY hXr hYr (hm i)) (by norm_num) (by norm_num) Λ A T

/-- **Level-α form.** Threshold `log(|Λ|/α)` gives false-alarm probability `≤ α` uniformly over
all sample sizes up to `T`. -/
theorem ville_two_arm_alpha {X Y : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (hXr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hYr : ∀ i ω, Y i ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun (fun i ω => (X i ω, Y i ω)) μ) (hm : ∀ i, μ[X i] = μ[Y i])
    (Λ : Finset ℝ) (hΛ : Λ.Nonempty) {α : ℝ} (hα : 0 < α) (T : ℕ) :
    μ.real {ω | ∃ l ∈ Λ, ∃ m ∈ Icc 1 T, log (Λ.card / α) ≤
        l * ∑ i ∈ range m, dif X Y i ω - m * log (1 + 1 / 2 * (exp l - 1))} ≤ α := by
  have hc : (0 : ℝ) < Λ.card := by exact_mod_cast hΛ.card_pos
  have := ville_two_arm hX hY hXr hYr hind hm Λ (log (Λ.card / α)) T
  rwa [exp_neg, exp_log (by positivity), inv_div, mul_div_cancel₀ _ hc.ne'] at this

end FiveOrgans.VilleTwoArm
