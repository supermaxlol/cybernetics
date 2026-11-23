import FiveOrgans.BernKL
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.ConditionalExpectation

/-!
# Time-uniform tail bounds (Ville's inequality via Doob)

For independent `[0,1]` draws `Z i` and a fixed tilt `l`, the product
`tm n = ∏_{i ≤ n} exp (l Z i) / mgf (Z i) l` is a nonnegative martingale for the natural
filtration of `Z` (`tm_martingale`). Doob's maximal inequality (`maximal_ineq` in Mathlib) then
gives `P(∃ k ≤ n, c ≤ tm k) ≤ 1/c` (`ville`): one bound for every sample size at once, with no
union over sizes.

With the Bernoulli mgf bound (`BernKL.mgf_le_bern`), `ville_bern` reads: for any `l` (negative `l`
gives the lower tail) and horizon `T`,
`P(∃ m ∈ 1..T, A ≤ l ∑_{i<m} Z i − m log(1 + p(e^l − 1))) ≤ e^{−A}`. `ville_bern_grid` unions over a
finite set of tilts, at cost `log |Λ|` instead of the `log T` that a union over sample sizes costs.

Assumption: the `Z i` are independent with common mean `p` (not necessarily identically distributed).
-/

namespace FiveOrgans.Ville
open MeasureTheory ProbabilityTheory Finset Real
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- One tilted factor. -/
noncomputable def g (Z : ℕ → Ω → ℝ) (μ : Measure Ω) (l : ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  exp (l * Z i ω) / mgf (Z i) μ l

/-- The tilted product over the first `n + 1` draws. -/
noncomputable def tm (Z : ℕ → Ω → ℝ) (μ : Measure Ω) (l : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ range (n + 1), g Z μ l i ω

theorem mul_le_abs {l y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) : l * y ≤ |l| :=
  calc l * y ≤ |l * y| := le_abs_self _
    _ = |l| * |y| := abs_mul _ _
    _ ≤ |l| * 1 := mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg hy.1]; exact hy.2) (abs_nonneg _)
    _ = |l| := mul_one _

theorem int_exp {Y : Ω → ℝ} (hY : Measurable Y) (hr : ∀ ω, Y ω ∈ Set.Icc (0 : ℝ) 1) (l : ℝ) :
    Integrable (fun ω => exp (l * Y ω)) μ :=
  Integrable.of_bound (C := exp |l|) (measurable_const.mul hY).exp.aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]; exact exp_le_exp.2 (mul_le_abs (hr ω)))

theorem mgf_pos' {Y : Ω → ℝ} (hY : Measurable Y) (hr : ∀ ω, Y ω ∈ Set.Icc (0 : ℝ) 1) (l : ℝ) :
    0 < mgf Y μ l :=
  mgf_pos (int_exp hY hr l)

section
variable {Z : ℕ → Ω → ℝ} (hZ : ∀ i, Measurable (Z i)) (hr : ∀ i ω, Z i ω ∈ Set.Icc (0 : ℝ) 1)
include hZ hr

theorem g_nonneg (l : ℝ) (i : ℕ) (ω : Ω) : 0 ≤ g Z μ l i ω :=
  div_nonneg (exp_pos _).le (mgf_pos' (hZ i) (hr i) l).le

theorem g_le (l : ℝ) (i : ℕ) (ω : Ω) : g Z μ l i ω ≤ exp |l| / mgf (Z i) μ l :=
  div_le_div_of_nonneg_right (exp_le_exp.2 (mul_le_abs (hr i ω))) (mgf_pos' (hZ i) (hr i) l).le

theorem g_int (l : ℝ) (i : ℕ) : Integrable (g Z μ l i) μ :=
  Integrable.of_bound (C := exp |l| / mgf (Z i) μ l)
    ((measurable_const.mul (hZ i)).exp.div_const _).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (g_nonneg hZ hr l i ω)]; exact g_le hZ hr l i ω)

theorem g_integral (l : ℝ) (i : ℕ) : μ[g Z μ l i] = 1 := by
  simp only [g]
  rw [integral_div]
  exact div_self (mgf_pos' (hZ i) (hr i) l).ne'

theorem tm_nonneg (l : ℝ) (n : ℕ) (ω : Ω) : 0 ≤ tm Z μ l n ω :=
  prod_nonneg fun i _ => g_nonneg hZ hr l i ω

theorem tm_int (l : ℝ) (n : ℕ) : Integrable (tm Z μ l n) μ :=
  Integrable.of_bound (C := ∏ i ∈ range (n + 1), exp |l| / mgf (Z i) μ l)
    (Finset.measurable_prod _ fun i _ =>
      (measurable_const.mul (hZ i)).exp.div_const _).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tm_nonneg hZ hr l n ω)]
      exact prod_le_prod₀ (fun i _ => g_nonneg hZ hr l i ω) fun i _ => g_le hZ hr l i ω)

theorem tm_eq (l : ℝ) (n : ℕ) (ω : Ω) :
    tm Z μ l n ω = exp (∑ i ∈ range (n + 1), (l * Z i ω - log (mgf (Z i) μ l))) := by
  rw [exp_sum, tm]
  refine prod_congr rfl fun i _ => ?_
  rw [g, exp_sub, exp_log (mgf_pos' (hZ i) (hr i) l)]

/-- The natural filtration of `Z`. -/
noncomputable def nat : MeasureTheory.Filtration ℕ mΩ :=
  MeasureTheory.Filtration.natural (fun i => Z i) fun i => (hZ i).stronglyMeasurable

omit hr in
theorem meas_nat {n j : ℕ} (hj : j ≤ n) : Measurable[nat hZ n] (Z j) :=
  measurable_iff_comap_le.2
    (le_iSup₂ (f := fun j (_ : j ≤ n) => MeasurableSpace.comap (Z j) inferInstance) j hj)

omit hr [IsProbabilityMeasure μ] in
theorem tm_sm (l : ℝ) (n : ℕ) : StronglyMeasurable[nat hZ n] (tm Z μ l n) :=
  (Finset.measurable_prod _ fun _j hj =>
    (measurable_const.mul (meas_nat hZ (Nat.lt_succ_iff.1 (mem_range.1 hj)))).exp.div_const
      _).stronglyMeasurable

theorem tm_martingale (hind : iIndepFun Z μ) (l : ℝ) : Martingale (tm Z μ l) (nat hZ) μ := by
  refine martingale_nat (fun n => ?_) (tm_int hZ hr l) fun i => ?_
  · exact tm_sm hZ l n
  have hsplit : tm Z μ l (i + 1) = tm Z μ l i * g Z μ l (i + 1) := by
    funext ω; simp only [tm, Pi.mul_apply]; rw [prod_range_succ]
  have hgm : StronglyMeasurable[MeasurableSpace.comap (Z (i + 1)) inferInstance] (g Z μ l (i + 1)) :=
    ((measurable_const.mul (comap_measurable (Z (i + 1)))).exp.div_const _).stronglyMeasurable
  have hI := (iIndepFun_iff_iIndep _ Z μ).1 hind
  have hdep := indep_iSup_of_disjoint (fun j => (hZ j).comap_le) hI
    (S := {i + 1}) (T := Set.Iic i) (Set.disjoint_singleton_left.2 (by simp))
  rw [_root_.iSup_singleton] at hdep
  have h3 := condExp_indep_eq (hZ (i + 1)).comap_le ((nat hZ).le i) hgm hdep
  have h2 := condExp_mul_of_stronglyMeasurable_left (m := nat hZ i) (μ := μ)
    (tm_sm hZ l i)
    (hsplit ▸ tm_int hZ hr l (i + 1)) (g_int hZ hr l (i + 1))
  rw [hsplit]
  filter_upwards [h2, h3] with ω a b
  rw [a, Pi.mul_apply, b, g_integral hZ hr, mul_one]

/-- **Ville's inequality** for the tilted product. -/
theorem ville (hind : iIndepFun Z μ) (l : ℝ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | ∃ k ≤ n, c ≤ tm Z μ l k ω} ≤ 1 / c := by
  have hm := tm_martingale hZ hr hind l
  have h := maximal_ineq hm.submartingale (fun k ω => tm_nonneg hZ hr l k ω) (ε := ⟨c, hc.le⟩) n
  have htot : ∫ ω, tm Z μ l n ω ∂μ = 1 := by
    have e := hm.setIntegral_eq (Nat.zero_le n) MeasurableSet.univ
    rw [setIntegral_univ, setIntegral_univ] at e
    rw [← e]
    simp only [tm, zero_add, prod_range_one]
    exact g_integral hZ hr l 0
  have hI : ∀ s : Set Ω, ∫ ω in s, tm Z μ l n ω ∂μ ≤ 1 := fun s =>
    htot ▸ setIntegral_le_integral (tm_int hZ hr l n) (ae_of_all _ fun ω => tm_nonneg hZ hr l n ω)
  have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h.trans (ENNReal.ofReal_le_ofReal (hI _)))
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal zero_le_one] at h'
  rw [le_div_iff₀ hc, mul_comm]
  refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono fun ω hω => ?_) hc.le) h'
  obtain ⟨k, hk, hck⟩ := hω
  have : c ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => tm Z μ l k ω :=
    (le_sup'_iff _).2 ⟨k, mem_range.2 (Nat.lt_succ_of_le hk), hck⟩
  exact this

omit hZ hr in
theorem bern_base_pos {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (l : ℝ) : 0 < 1 + p * (exp l - 1) :=
  BernKL.bern_pos hp0 hp1 l (by
    rcases lt_or_ge p 1 with h | h
    · exact Or.inr h
    · exact Or.inl (by linarith))

/-- **Time-uniform Bernoulli-mgf bound.** One tilt `l`, every sample size `m ≤ T` at once. -/
theorem ville_bern (hind : iIndepFun Z μ) {p : ℝ} (hm : ∀ i, μ[Z i] = p) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (l A : ℝ) (T : ℕ) :
    μ.real {ω | ∃ m ∈ Icc 1 T, A ≤ l * ∑ i ∈ range m, Z i ω - m * log (1 + p * (exp l - 1))}
      ≤ exp (-A) := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · have : {ω | ∃ m ∈ Icc 1 0, A ≤ l * ∑ i ∈ range m, Z i ω - m * log (1 + p * (exp l - 1))}
        = ∅ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro m hm; have := mem_Icc.1 hm; omega
    rw [this, measureReal_empty]; exact (exp_pos _).le
  have hb := bern_base_pos hp0 hp1 l
  calc _ ≤ μ.real {ω | ∃ k ≤ T - 1, exp A ≤ tm Z μ l k ω} := measureReal_mono fun ω hω => by
        obtain ⟨m, hmI, hA⟩ := hω
        obtain ⟨h1, h2⟩ := mem_Icc.1 hmI
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        refine ⟨k, by omega, ?_⟩
        rw [tm_eq hZ hr, exp_le_exp, sum_sub_distrib, ← mul_sum]
        have : ∑ i ∈ range (k + 1), log (mgf (Z i) μ l)
            ≤ ((k + 1 : ℕ) : ℝ) * log (1 + p * (exp l - 1)) := by
          calc _ ≤ ∑ _i ∈ range (k + 1), log (1 + p * (exp l - 1)) :=
                sum_le_sum fun i _ => log_le_log (mgf_pos' (hZ i) (hr i) l)
                  (BernKL.mgf_le_bern (hZ i) (hr i) (hm i) l)
            _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
        linarith
    _ ≤ 1 / exp A := ville hZ hr hind l (T - 1) (exp_pos A)
    _ = exp (-A) := by rw [exp_neg, one_div]

/-- **Finite grid of tilts.** Union over `Λ` costs `|Λ|`, not the horizon `T`. -/
theorem ville_bern_grid (hind : iIndepFun Z μ) {p : ℝ} (hm : ∀ i, μ[Z i] = p) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (Λ : Finset ℝ) (A : ℝ) (T : ℕ) :
    μ.real {ω | ∃ l ∈ Λ, ∃ m ∈ Icc 1 T,
        A ≤ l * ∑ i ∈ range m, Z i ω - m * log (1 + p * (exp l - 1))} ≤ Λ.card * exp (-A) := by
  calc _ = μ.real (⋃ l ∈ Λ, {ω | ∃ m ∈ Icc 1 T,
          A ≤ l * ∑ i ∈ range m, Z i ω - m * log (1 + p * (exp l - 1))}) := by
        congr 1; ext ω; simp
    _ ≤ ∑ l ∈ Λ, μ.real {ω | ∃ m ∈ Icc 1 T,
          A ≤ l * ∑ i ∈ range m, Z i ω - m * log (1 + p * (exp l - 1))} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _l ∈ Λ, exp (-A) := sum_le_sum fun l _ => ville_bern hZ hr hind hm hp0 hp1 l A T
    _ = _ := by rw [sum_const, nsmul_eq_mul]

end

end FiveOrgans.Ville
