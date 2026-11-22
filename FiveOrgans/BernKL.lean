import FiveOrgans.PoissonFlip
import FiveOrgans.PoissonRandom

/-!
# The Bernoulli-KL (Chernoff–Hoeffding relative-entropy) bound and tests built on it

For independent `[0,1]` variables with common mean `p ∈ (0,1)`:
`P(p̂ ≥ a) ≤ exp (−N · kl(a ‖ p))`, `kl(a ‖ p) = a log (a/p) + (1−a) log ((1−a)/(1−p))`.
This is the standard relative-entropy form of the Chernoff–Hoeffding bound (stated, for
example, in Kakade's Stat 928 notes and Mulzer's survey of Chernoff proofs). It is sharper
than the Poisson exponent of `PoissonTail` (`poisKL_le_binKL`) and symmetric under
`a, p ↦ 1−a, 1−p` (`binKL_symm`). So ONE test covers means near 0 and near 1, with no
orientation union (compare `PoissonFlip`, which pays `8 e^{−L}`).

* `mgf_le_bern` — `E e^{sX} ≤ 1 + p (eˢ − 1)` (the chord, integrated); `mgf_sum_bern`.
* `upper_tail_bern` — `P(S ≥ N a) ≤ exp (−N (t a − log (1 + p(eᵗ − 1))))` for `t ≥ 0`.
* `upper_opt_bern` (`p ≤ a < 1`), `upper_one_bern` (`a = 1`, limit `t → ∞`):
  `P(S ≥ N a) ≤ exp (−N · binKL a p)`.
* `binKL_symm`, `binKL_cont`, `poisKL_le_binKL`.
* `kl_upper_bern`, `kl_lower_bern` (lower = upper for `1 − X`), `kl_conf_bern` (`≤ 2e^{−L}`),
  `kl_two_sample_bern` (`≤ 4e^{−L}`, any dependence between samples) and calibrated forms;
  `kl_conf_bern_random`, `kl_two_sample_bern_random_alpha` (random counts in `1..T`,
  `L = log (4T/α)`).

Same assumption as before: independent draws with a common mean. It does not make logged
data i.i.d.
-/

namespace FiveOrgans.BernKL
open MeasureTheory ProbabilityTheory Finset Real Filter Topology
open FiveOrgans.PoissonTail FiveOrgans.PoissonConf FiveOrgans.PoissonFlip FiveOrgans.RandomCount
open FiveOrgans.PoissonRandom

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem mgf_le_bern {Y : Ω → ℝ} (hY : Measurable Y) (hr : ∀ ω, Y ω ∈ Set.Icc (0 : ℝ) 1)
    {p : ℝ} (hm : μ[Y] = p) (s : ℝ) : mgf Y μ s ≤ 1 + p * (exp s - 1) := by
  have hYi : Integrable Y μ :=
    Integrable.of_bound (C := 1) hY.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hr ω).1]; exact (hr ω).2)
  calc mgf Y μ s = μ[fun ω => exp (s * Y ω)] := rfl
    _ ≤ μ[fun ω => 1 + Y ω * (exp s - 1)] :=
        integral_mono (integrable_exp hY hr s) ((integrable_const 1).add (hYi.mul_const _))
          fun ω => exp_le_chord s (hr ω)
    _ = 1 + p * (exp s - 1) := by
        rw [integral_add (integrable_const 1) (hYi.mul_const _), integral_mul_const, hm]
        simp

theorem bern_pos {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ) (hp : 0 < p ∨ p < 1) :
    0 < 1 + p * (exp s - 1) := by
  have he := exp_pos s
  rcases hp with h | h
  · nlinarith [mul_pos h he]
  · nlinarith [mul_nonneg hp0 he.le]

theorem mgf_sum_bern {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (hp : 0 < p)
    (hp1 : p ≤ 1) (N : ℕ) (s : ℝ) :
    mgf (∑ i ∈ range N, X i) μ s ≤ exp (N * log (1 + p * (exp s - 1))) := by
  have hc := bern_pos hp.le hp1 s (Or.inl hp)
  rw [hind.mgf_sum hX]
  calc ∏ i ∈ range N, mgf (X i) μ s ≤ ∏ _i ∈ range N, (1 + p * (exp s - 1)) := by
        gcongr
        · intro i _; exact mgf_nonneg
        · exact mgf_le_bern (hX _) (hr _) (hm _) s
    _ = exp (N * log (1 + p * (exp s - 1))) := by
        rw [prod_const, card_range, exp_nat_mul, exp_log hc]

omit [MeasurableSpace Ω] in
theorem sum_range_mem {X : ℕ → Ω → ℝ} (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) (N : ℕ) (ω : Ω) :
    (∑ i ∈ range N, X i) ω ∈ Set.Icc (0 : ℝ) N := by
  simp only [Finset.sum_apply]
  constructor
  · exact sum_nonneg fun i _ => (hr i ω).1
  · calc ∑ i ∈ range N, X i ω ≤ ∑ _i ∈ range N, (1 : ℝ) := sum_le_sum fun i _ => (hr i ω).2
      _ = N := by simp

/-- **Upper tail, Bernoulli form, any `t ≥ 0`.** -/
theorem upper_tail_bern {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (hp : 0 < p)
    (hp1 : p ≤ 1) (N : ℕ) (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | N * a ≤ ∑ i ∈ range N, X i ω}
      ≤ exp (-(N * (t * a - log (1 + p * (exp t - 1))))) := by
  have hint : Integrable (fun ω => exp (t * (∑ i ∈ range N, X i) ω)) μ := by
    refine Integrable.of_bound (C := exp (|t| * N)) (by fun_prop) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.2
    have := sum_range_mem hr N ω
    calc t * _ ≤ |t * (∑ i ∈ range N, X i) ω| := le_abs_self _
      _ = |t| * (∑ i ∈ range N, X i) ω := by rw [abs_mul, abs_of_nonneg this.1]
      _ ≤ |t| * N := mul_le_mul_of_nonneg_left this.2 (abs_nonneg _)
  have h := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ range N, X i) (N * a) ht hint
  have hset : {ω | N * a ≤ ∑ i ∈ range N, X i ω} = {ω | N * a ≤ (∑ i ∈ range N, X i) ω} := by
    ext ω; simp [Finset.sum_apply]
  rw [hset]
  refine h.trans ?_
  calc exp (-t * (N * a)) * mgf (∑ i ∈ range N, X i) μ t
      ≤ exp (-t * (N * a)) * exp (N * log (1 + p * (exp t - 1))) :=
        mul_le_mul_of_nonneg_left (mgf_sum_bern hX hind hr hm hp hp1 N t) (exp_pos _).le
    _ = exp (-(N * (t * a - log (1 + p * (exp t - 1))))) := by rw [← exp_add]; ring_nf

/-- The Bernoulli relative entropy `kl(a ‖ p)`. -/
noncomputable def binKL (a p : ℝ) : ℝ := a * log (a / p) + (1 - a) * log ((1 - a) / (1 - p))

theorem binKL_symm (a p : ℝ) : binKL (1 - a) (1 - p) = binKL a p := by
  unfold binKL; simp only [sub_sub_cancel]; ring

/-- **Upper tail, optimised:** `p ≤ a < 1` ⇒ `P(S ≥ N a) ≤ exp (−N · kl(a ‖ p))`. -/
theorem upper_opt_bern {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (hp : 0 < p)
    (hp1 : p < 1) (N : ℕ) {a : ℝ} (hpa : p ≤ a) (ha1 : a < 1) :
    μ.real {ω | N * a ≤ ∑ i ∈ range N, X i ω} ≤ exp (-(N * binKL a p)) := by
  have ha : 0 < a := hp.trans_le hpa
  have h1a : 0 < 1 - a := by linarith
  have h1p : 0 < 1 - p := by linarith
  set r := a * (1 - p) / (p * (1 - a)) with hr_def
  have hrpos : 0 < r := by positivity
  have hr1 : 1 ≤ r := by
    rw [hr_def, one_le_div (by positivity)]; nlinarith
  have ht : 0 ≤ log r := log_nonneg hr1
  have h := upper_tail_bern hX hind hr hm hp hp1.le N a ht
  have hc : 1 + p * (exp (log r) - 1) = (1 - p) / (1 - a) := by
    have := h1a.ne'; have := hp.ne'
    rw [exp_log hrpos, hr_def]; field_simp; ring
  rw [hc] at h
  have hlr : log r = log a + log (1 - p) - log p - log (1 - a) := by
    rw [hr_def, log_div (mul_pos ha h1p).ne' (mul_pos hp h1a).ne', log_mul ha.ne' h1p.ne',
      log_mul hp.ne' h1a.ne']; ring
  refine h.trans_eq (congrArg exp ?_)
  unfold binKL
  rw [hlr, log_div ha.ne' hp.ne', log_div h1a.ne' h1p.ne', log_div h1p.ne' h1a.ne']
  ring

theorem binKL_one (p : ℝ) : binKL 1 p = -log p := by
  unfold binKL; simp [one_div, log_inv]

/-- **`a = 1`:** `P(S ≥ N) ≤ pᴺ = exp (−N · kl(1 ‖ p))` (limit `t → ∞`). -/
theorem upper_one_bern {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (hp : 0 < p)
    (hp1 : p ≤ 1) (N : ℕ) :
    μ.real {ω | N * 1 ≤ ∑ i ∈ range N, X i ω} ≤ exp (-(N * binKL 1 p)) := by
  have hform : ∀ t : ℝ, t * 1 - log (1 + p * (exp t - 1)) = -log ((1 - p) * exp (-t) + p) := by
    intro t
    have h1p : 0 ≤ 1 - p := by linarith
    have hpos : 0 < (1 - p) * exp (-t) + p := by
      have := mul_nonneg h1p (exp_pos (-t)).le; linarith
    have hee : exp t * exp (-t) = 1 := by rw [← exp_add]; simp
    have : 1 + p * (exp t - 1) = exp t * ((1 - p) * exp (-t) + p) := by
      linear_combination (-(1 - p)) * hee
    rw [this, log_mul (exp_pos t).ne' hpos.ne', log_exp]; ring
  have key : ∀ᶠ t in atTop, μ.real {ω | N * 1 ≤ ∑ i ∈ range N, X i ω}
      ≤ exp (-(N * -log ((1 - p) * exp (-t) + p))) :=
    (eventually_ge_atTop 0).mono fun t ht => by
      have := upper_tail_bern hX hind hr hm hp hp1 N 1 ht
      rwa [hform t] at this
  have tend : Tendsto (fun t : ℝ => exp (-(N * -log ((1 - p) * exp (-t) + p)))) atTop
      (𝓝 (exp (-(N * binKL 1 p)))) := by
    have h0 : Tendsto (fun t : ℝ => (1 - p) * exp (-t) + p) atTop (𝓝 p) := by
      have := (tendsto_exp_neg_atTop_nhds_zero.const_mul (1 - p)).add_const p
      simpa using this
    have := ((h0.log hp.ne').neg.const_mul (N : ℝ)).neg.rexp
    rw [binKL_one]; exact this
  exact ge_of_tendsto tend key

theorem binKL_cont {p : ℝ} (hp : p ≠ 0) (hp1 : 1 - p ≠ 0) : Continuous fun a => binKL a p := by
  have e1 : ∀ a : ℝ, p * (a / p) = a := fun a => by field_simp
  have e2 : ∀ a : ℝ, (1 - p) * ((1 - a) / (1 - p)) = 1 - a := fun a => by field_simp
  have e : ∀ a, binKL a p = p * ((a / p) * log (a / p)) +
      (1 - p) * (((1 - a) / (1 - p)) * log ((1 - a) / (1 - p))) := fun a => by
    unfold binKL; rw [← mul_assoc, e1, ← mul_assoc, e2]
  simp_rw [e]
  exact (continuous_const.mul (continuous_mul_log.comp (continuous_id.div_const p))).add
    (continuous_const.mul (continuous_mul_log.comp ((continuous_const.sub continuous_id).div_const _)))

/-- **Sharper than Poisson:** `poisKL a p ≤ kl(a ‖ p)` on `[0,1]`. -/
theorem poisKL_le_binKL {a p : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hp1 : p < 1) :
    poisKL a p ≤ binKL a p := by
  unfold poisKL binKL
  rcases ha1.lt_or_eq with ha | ha
  · have h1a : 0 < 1 - a := by linarith
    have h1p : 0 < 1 - p := by linarith
    have hl := one_sub_inv_le_log_of_pos (div_pos h1a h1p)
    rw [inv_div] at hl
    have hm := mul_le_mul_of_nonneg_left hl h1a.le
    have he : (1 - a) * (1 - (1 - p) / (1 - a)) = p - a := by
      have := h1a.ne'; field_simp; ring
    rw [he] at hm; linarith
  · subst ha
    have : (1 - (1 : ℝ)) * log ((1 - 1) / (1 - p)) = 0 := by ring
    linarith

/-- **Upper half of the Bernoulli-KL confidence statement.** -/
theorem kl_upper_bern {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) {N : ℕ} (hN : 0 < N)
    (hp : 0 < p) (hp1 : p < 1) (L : ℝ) :
    μ.real {ω | p ≤ (∑ i ∈ range N, X i ω) / N ∧ L ≤ N * binKL ((∑ i ∈ range N, X i ω) / N) p}
      ≤ exp (-L) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hS1 : ∀ ω, (∑ i ∈ range N, X i ω) / N ≤ 1 := fun ω => by
    rw [div_le_one hN']
    have := (sum_range_mem hr N ω).2
    simpa [Finset.sum_apply] using this
  set A : Set ℝ := {a | p ≤ a ∧ a ≤ 1 ∧ L ≤ N * binKL a p} with hAdef
  by_cases hA : A.Nonempty
  · have hcl : IsClosed A := (isClosed_le continuous_const continuous_id).inter
      ((isClosed_le continuous_id continuous_const).inter
        (isClosed_le continuous_const
          (continuous_const.mul (binKL_cont hp.ne' (by linarith : (1 : ℝ) - p ≠ 0)))))
    have hbdd : BddBelow A := ⟨p, fun a ha => ha.1⟩
    have ha0 : sInf A ∈ A := hcl.csInf_mem hA hbdd
    have hmono : μ.real {ω | p ≤ (∑ i ∈ range N, X i ω) / N ∧
        L ≤ N * binKL ((∑ i ∈ range N, X i ω) / N) p}
        ≤ μ.real {ω | N * sInf A ≤ ∑ i ∈ range N, X i ω} := by
      refine measureReal_mono (fun ω hω => ?_)
      obtain ⟨h1, h2⟩ := hω
      have h3 : sInf A ≤ (∑ i ∈ range N, X i ω) / N := csInf_le hbdd ⟨h1, hS1 ω, h2⟩
      rw [le_div_iff₀ hN'] at h3
      show (N : ℝ) * sInf A ≤ ∑ i ∈ range N, X i ω
      linarith
    refine hmono.trans ?_
    obtain ⟨hA1, hA2, hA3⟩ := ha0
    rcases hA2.lt_or_eq with hlt | heq
    · exact (upper_opt_bern hX hind hr hm hp hp1 N hA1 hlt).trans (exp_le_exp.2 (by linarith))
    · rw [heq] at hA3 ⊢
      exact (upper_one_bern hX hind hr hm hp hp1.le N).trans (exp_le_exp.2 (by linarith))
  · calc _ ≤ μ.real (∅ : Set Ω) :=
          measureReal_mono (fun ω hω => (hA ⟨_, hω.1, hS1 ω, hω.2⟩).elim)
      _ ≤ exp (-L) := by rw [measureReal_empty]; positivity

omit [MeasurableSpace Ω] in
theorem flip_avg (X : ℕ → Ω → ℝ) {N : ℕ} (hN : 0 < N) (ω : Ω) :
    (∑ i ∈ range N, (1 - X i ω)) / N = 1 - (∑ i ∈ range N, X i ω) / N := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one, sub_div, div_self hN']

/-- **Lower half:** the upper half applied to `1 − X` (mean `1 − p`), via `binKL_symm`. -/
theorem kl_lower_bern {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) {N : ℕ} (hN : 0 < N)
    (hp : 0 < p) (hp1 : p < 1) (L : ℝ) :
    μ.real {ω | (∑ i ∈ range N, X i ω) / N ≤ p ∧ L ≤ N * binKL ((∑ i ∈ range N, X i ω) / N) p}
      ≤ exp (-L) := by
  refine le_trans (measureReal_mono fun ω hω => ?_)
    (kl_upper_bern (flip_measurable hX) (flip_indep hind) (flip_range hr) (flip_mean hX hr hm)
      hN (by linarith : (0 : ℝ) < 1 - p) (by linarith : 1 - p < 1) L)
  obtain ⟨h1, h2⟩ := hω
  refine ⟨?_, ?_⟩
  · show 1 - p ≤ (∑ i ∈ range N, (1 - X i ω)) / N
    rw [flip_avg X hN ω]; linarith
  · show L ≤ N * binKL ((∑ i ∈ range N, (1 - X i ω)) / N) (1 - p)
    rw [flip_avg X hN ω, binKL_symm]; exact h2

/-- **Bernoulli-KL confidence statement:** `P(N · kl(p̂ ‖ p) ≥ L) ≤ 2 e^{−L}`. -/
theorem kl_conf_bern {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) {N : ℕ} (hN : 0 < N)
    (hp : 0 < p) (hp1 : p < 1) (L : ℝ) :
    μ.real {ω | L ≤ N * binKL ((∑ i ∈ range N, X i ω) / N) p} ≤ 2 * exp (-L) := by
  calc _ ≤ μ.real ({ω | p ≤ (∑ i ∈ range N, X i ω) / N ∧
              L ≤ N * binKL ((∑ i ∈ range N, X i ω) / N) p} ∪
            {ω | (∑ i ∈ range N, X i ω) / N ≤ p ∧
              L ≤ N * binKL ((∑ i ∈ range N, X i ω) / N) p}) := by
          refine measureReal_mono (fun ω hω => ?_)
          rcases le_total p ((∑ i ∈ range N, X i ω) / N) with h | h
          · exact Or.inl ⟨h, hω⟩
          · exact Or.inr ⟨h, hω⟩
    _ ≤ _ + _ := measureReal_union_le _ _
    _ ≤ exp (-L) + exp (-L) := add_le_add (kl_upper_bern hX hind hr hm hN hp hp1 L)
          (kl_lower_bern hX hind hr hm hN hp hp1 L)
    _ = 2 * exp (-L) := by ring

theorem kl_conf_bern_alpha {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) {N : ℕ} (hN : 0 < N)
    (hp : 0 < p) (hp1 : p < 1) {α : ℝ} (hα : 0 < α) :
    μ.real {ω | log (2 / α) ≤ N * binKL ((∑ i ∈ range N, X i ω) / N) p} ≤ α := by
  refine (kl_conf_bern hX hind hr hm hN hp hp1 _).trans_eq ?_
  rw [exp_neg_log (by positivity)]; field_simp

/-- **Two-sample Bernoulli-KL test** (any dependence between the samples): `≤ 4 e^{−L}`. -/
theorem kl_two_sample_bern {X₁ X₂ : ℕ → Ω → ℝ} (hX₁ : ∀ i, Measurable (X₁ i))
    (hX₂ : ∀ i, Measurable (X₂ i)) (hind₁ : iIndepFun X₁ μ) (hind₂ : iIndepFun X₂ μ)
    (hr₁ : ∀ i ω, X₁ i ω ∈ Set.Icc (0 : ℝ) 1) (hr₂ : ∀ i ω, X₂ i ω ∈ Set.Icc (0 : ℝ) 1)
    {p : ℝ} (hm₁ : ∀ i, μ[X₁ i] = p) (hm₂ : ∀ i, μ[X₂ i] = p) {N₁ N₂ : ℕ} (hN₁ : 0 < N₁)
    (hN₂ : 0 < N₂) (hp : 0 < p) (hp1 : p < 1) (L : ℝ) :
    μ.real {ω | ∀ q, 0 < q → q < 1 → L ≤ N₁ * binKL ((∑ i ∈ range N₁, X₁ i ω) / N₁) q ∨
                               L ≤ N₂ * binKL ((∑ i ∈ range N₂, X₂ i ω) / N₂) q}
      ≤ 4 * exp (-L) := by
  calc _ ≤ μ.real ({ω | L ≤ N₁ * binKL ((∑ i ∈ range N₁, X₁ i ω) / N₁) p} ∪
            {ω | L ≤ N₂ * binKL ((∑ i ∈ range N₂, X₂ i ω) / N₂) p}) :=
          measureReal_mono (fun ω hω => by simp only [Set.mem_ofPred_eq] at hω; exact hω p hp hp1)
    _ ≤ _ + _ := measureReal_union_le _ _
    _ ≤ 2 * exp (-L) + 2 * exp (-L) := add_le_add (kl_conf_bern hX₁ hind₁ hr₁ hm₁ hN₁ hp hp1 L)
          (kl_conf_bern hX₂ hind₂ hr₂ hm₂ hN₂ hp hp1 L)
    _ = 4 * exp (-L) := by ring

theorem kl_two_sample_bern_alpha {X₁ X₂ : ℕ → Ω → ℝ} (hX₁ : ∀ i, Measurable (X₁ i))
    (hX₂ : ∀ i, Measurable (X₂ i)) (hind₁ : iIndepFun X₁ μ) (hind₂ : iIndepFun X₂ μ)
    (hr₁ : ∀ i ω, X₁ i ω ∈ Set.Icc (0 : ℝ) 1) (hr₂ : ∀ i ω, X₂ i ω ∈ Set.Icc (0 : ℝ) 1)
    {p : ℝ} (hm₁ : ∀ i, μ[X₁ i] = p) (hm₂ : ∀ i, μ[X₂ i] = p) {N₁ N₂ : ℕ} (hN₁ : 0 < N₁)
    (hN₂ : 0 < N₂) (hp : 0 < p) (hp1 : p < 1) {α : ℝ} (hα : 0 < α) :
    μ.real {ω | ∀ q, 0 < q → q < 1 →
        log (4 / α) ≤ N₁ * binKL ((∑ i ∈ range N₁, X₁ i ω) / N₁) q ∨
        log (4 / α) ≤ N₂ * binKL ((∑ i ∈ range N₂, X₂ i ω) / N₂) q} ≤ α := by
  refine (kl_two_sample_bern hX₁ hX₂ hind₁ hind₂ hr₁ hr₂ hm₁ hm₂ hN₁ hN₂ hp hp1 _).trans_eq ?_
  rw [exp_neg_log (by positivity)]; field_simp

/-- **Random count.** -/
theorem kl_conf_bern_random {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (hp : 0 < p)
    (hp1 : p < 1) (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) (N : Ω → ℕ) (hN : ∀ ω, N ω ∈ S) (L : ℝ) :
    μ.real {ω | L ≤ N ω * binKL ((∑ i ∈ range (N ω), X i ω) / N ω) p}
      ≤ S.card * (2 * exp (-L)) := by
  let bad : ℕ → Set Ω := fun n => {ω | L ≤ n * binKL ((∑ i ∈ range n, X i ω) / n) p}
  calc _ = μ.real {ω | ω ∈ bad (N ω)} := rfl
    _ ≤ ∑ n ∈ S, μ.real (bad n) := random_index_le bad S N hN
    _ ≤ ∑ _n ∈ S, 2 * exp (-L) :=
        sum_le_sum fun n hn => kl_conf_bern hX hind hr hm (hS n hn) hp hp1 L
    _ = S.card * (2 * exp (-L)) := by rw [sum_const, nsmul_eq_mul]

/-- **Two-sample, random counts in `1..T`, calibrated:** `L = log (4T/α)`. -/
theorem kl_two_sample_bern_random_alpha {X₁ X₂ : ℕ → Ω → ℝ} (hX₁ : ∀ i, Measurable (X₁ i))
    (hX₂ : ∀ i, Measurable (X₂ i)) (hind₁ : iIndepFun X₁ μ) (hind₂ : iIndepFun X₂ μ)
    (hr₁ : ∀ i ω, X₁ i ω ∈ Set.Icc (0 : ℝ) 1) (hr₂ : ∀ i ω, X₂ i ω ∈ Set.Icc (0 : ℝ) 1)
    {p : ℝ} (hm₁ : ∀ i, μ[X₁ i] = p) (hm₂ : ∀ i, μ[X₂ i] = p) (hp : 0 < p) (hp1 : p < 1)
    {T : ℕ} (hT : 0 < T) (N₁ N₂ : Ω → ℕ) (hN₁ : ∀ ω, N₁ ω ∈ Icc 1 T) (hN₂ : ∀ ω, N₂ ω ∈ Icc 1 T)
    {α : ℝ} (hα : 0 < α) :
    μ.real {ω | ∀ q, 0 < q → q < 1 →
        log (4 * T / α) ≤ N₁ ω * binKL ((∑ i ∈ range (N₁ ω), X₁ i ω) / N₁ ω) q ∨
        log (4 * T / α) ≤ N₂ ω * binKL ((∑ i ∈ range (N₂ ω), X₂ i ω) / N₂ ω) q} ≤ α := by
  have hT' : (0 : ℝ) < T := Nat.cast_pos.2 hT
  have hS : ∀ n ∈ Icc 1 T, 0 < n := fun n hn => pos_of_Icc hn
  calc _ ≤ μ.real ({ω | log (4 * T / α) ≤
              N₁ ω * binKL ((∑ i ∈ range (N₁ ω), X₁ i ω) / N₁ ω) p} ∪
            {ω | log (4 * T / α) ≤ N₂ ω * binKL ((∑ i ∈ range (N₂ ω), X₂ i ω) / N₂ ω) p}) :=
          measureReal_mono (fun ω hω => by simp only [Set.mem_ofPred_eq] at hω; exact hω p hp hp1)
    _ ≤ _ + _ := measureReal_union_le _ _
    _ ≤ (Icc 1 T).card * (2 * exp (-log (4 * T / α))) +
          (Icc 1 T).card * (2 * exp (-log (4 * T / α))) :=
        add_le_add (kl_conf_bern_random hX₁ hind₁ hr₁ hm₁ hp hp1 _ hS N₁ hN₁ _)
          (kl_conf_bern_random hX₂ hind₂ hr₂ hm₂ hp hp1 _ hS N₂ hN₂ _)
    _ = α := by rw [card_Icc_one, exp_neg_log (by positivity)]; field_simp; ring

end FiveOrgans.BernKL
