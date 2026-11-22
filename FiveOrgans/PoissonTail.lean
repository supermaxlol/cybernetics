import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A variance-adaptive tail bound for counts (Chernoff with a Poisson exponent)

The φ-test modules (`RowConcentration`, `CrossScaleContrast`, `DiffContrast`, `RandomCount`)
use Hoeffding, whose exponent `2N(a − p)²` ignores how small `p` is. For rare events (hazards,
transition probabilities of a few percent) that wastes most of the sample: the real 2024 runs
were INCONCLUSIVE largely because of this (TASKS 24u).

Setting: `X 0, X 1, …` independent, each with values in `[0, 1]` and mean `p`.

* `exp_le_chord` — convexity: `exp (s x) ≤ 1 + x (eˢ − 1)` on `[0, 1]`, for every real `s`.
* `mgf_le` — `E[exp (s X)] ≤ exp (p (eˢ − 1))` (a `[0,1]` variable is dominated by Poisson).
* `upper_tail`, `lower_tail` — Chernoff: for every `t ≥ 0`,
  `P(Σ X ≥ N a) ≤ exp (−N (t a − p (eᵗ − 1)))` and
  `P(Σ X ≤ N a) ≤ exp (−N (−t a − p (e⁻ᵗ − 1)))`.
* `poisKL a p = a log (a/p) − a + p` — the optimised exponent.
  `upper_opt` (`p < a`) and `lower_opt` (`0 < a < p`): **`P ≤ exp (−N · poisKL a p)`**.
* `upper_alpha`, `lower_alpha`, `two_sided_alpha` — calibrated forms: if `N · poisKL ≥ log (1/α)`
  the tail is at most `α` (two sides: `2α`).
* `poisKL_ge` — for `p ≤ a`, `poisKL a p ≥ (a − p)² / (2a)`; `beats_hoeffding` — for
  `a ≤ 1/(4c)` the exponent is at least `c` times Hoeffding's `2(a − p)²`.

Same assumption as the other modules: independent draws with a common mean. It does not make
logged data i.i.d.
-/

namespace FiveOrgans.PoissonTail
open MeasureTheory ProbabilityTheory Finset Real

/-- Chord above `exp` on `[0,1]`. -/
theorem exp_le_chord (s : ℝ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    exp (s * x) ≤ 1 + x * (exp s - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ s) (sub_nonneg.2 hx.2) hx.1
    (by ring : (1 - x) + x = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] at h
  calc exp (s * x) = exp (x * s) := by rw [mul_comm]
    _ ≤ 1 - x + x * exp s := h
    _ = 1 + x * (exp s - 1) := by ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integrable_exp {Y : Ω → ℝ} (hY : Measurable Y) (hr : ∀ ω, Y ω ∈ Set.Icc (0 : ℝ) 1)
    (s : ℝ) : Integrable (fun ω => exp (s * Y ω)) μ := by
  refine Integrable.of_bound (C := exp |s|) (by fun_prop) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  apply exp_le_exp.2
  have := hr ω
  calc s * Y ω ≤ |s * Y ω| := le_abs_self _
    _ = |s| * Y ω := by rw [abs_mul, abs_of_nonneg this.1]
    _ ≤ |s| * 1 := mul_le_mul_of_nonneg_left this.2 (abs_nonneg _)
    _ = |s| := mul_one _

/-- **Poisson domination of the mgf.** -/
theorem mgf_le {Y : Ω → ℝ} (hY : Measurable Y) (hr : ∀ ω, Y ω ∈ Set.Icc (0 : ℝ) 1)
    {p : ℝ} (hm : μ[Y] = p) (s : ℝ) : mgf Y μ s ≤ exp (p * (exp s - 1)) := by
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
    _ ≤ exp (p * (exp s - 1)) := by linarith [add_one_le_exp (p * (exp s - 1))]

theorem mgf_sum_le {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (N : ℕ) (s : ℝ) :
    mgf (∑ i ∈ range N, X i) μ s ≤ exp (N * (p * (exp s - 1))) := by
  rw [hind.mgf_sum hX]
  calc ∏ i ∈ range N, mgf (X i) μ s ≤ ∏ _i ∈ range N, exp (p * (exp s - 1)) := by
        gcongr
        · intro i _; exact mgf_nonneg
        · exact mgf_le (hX _) (hr _) (hm _) s
    _ = exp (N * (p * (exp s - 1))) := by rw [prod_const, card_range, ← exp_nat_mul]

/-- **Upper tail, any `t ≥ 0`.** -/
theorem upper_tail {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (N : ℕ)
    (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | N * a ≤ ∑ i ∈ range N, X i ω} ≤ exp (-(N * (t * a - p * (exp t - 1)))) := by
  have hSr : ∀ ω, (∑ i ∈ range N, X i) ω ∈ Set.Icc (0 : ℝ) N := fun ω => by
    simp only [Finset.sum_apply]
    constructor
    · exact sum_nonneg fun i _ => (hr i ω).1
    · calc ∑ i ∈ range N, X i ω ≤ ∑ _i ∈ range N, (1 : ℝ) := sum_le_sum fun i _ => (hr i ω).2
        _ = N := by simp
  have hint : Integrable (fun ω => exp (t * (∑ i ∈ range N, X i) ω)) μ := by
    refine Integrable.of_bound (C := exp (|t| * N)) (by fun_prop) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.2
    have := hSr ω
    calc t * _ ≤ |t * (∑ i ∈ range N, X i) ω| := le_abs_self _
      _ = |t| * (∑ i ∈ range N, X i) ω := by rw [abs_mul, abs_of_nonneg this.1]
      _ ≤ |t| * N := mul_le_mul_of_nonneg_left this.2 (abs_nonneg _)
  have h := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ range N, X i) (N * a) ht hint
  have hset : {ω | N * a ≤ ∑ i ∈ range N, X i ω} = {ω | N * a ≤ (∑ i ∈ range N, X i) ω} := by
    ext ω; simp [Finset.sum_apply]
  rw [hset]
  refine h.trans ?_
  calc exp (-t * (N * a)) * mgf (∑ i ∈ range N, X i) μ t
      ≤ exp (-t * (N * a)) * exp (N * (p * (exp t - 1))) :=
        mul_le_mul_of_nonneg_left (mgf_sum_le hX hind hr hm N t) (exp_pos _).le
    _ = exp (-(N * (t * a - p * (exp t - 1)))) := by rw [← exp_add]; ring_nf

/-- **Lower tail, any `t ≥ 0`** (apply `upper_tail` to `1 − X`, then rewrite). -/
theorem lower_tail {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (N : ℕ)
    (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∑ i ∈ range N, X i ω ≤ N * a} ≤ exp (-(N * (-t * a - p * (exp (-t) - 1)))) := by
  set Y : ℕ → Ω → ℝ := fun i ω => -X i ω
  have hY : ∀ i, Measurable (Y i) := fun i => (hX i).neg
  have hindY : iIndepFun Y μ := hind.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hSr : ∀ ω, (∑ i ∈ range N, Y i) ω ∈ Set.Icc (-(N : ℝ)) 0 := fun ω => by
    simp only [Finset.sum_apply, Y, sum_neg_distrib]
    constructor
    · have : ∑ i ∈ range N, X i ω ≤ N := by
        calc ∑ i ∈ range N, X i ω ≤ ∑ _i ∈ range N, (1 : ℝ) := sum_le_sum fun i _ => (hr i ω).2
          _ = N := by simp
      linarith
    · linarith [sum_nonneg fun i (_ : i ∈ range N) => (hr i ω).1]
  have hint : Integrable (fun ω => exp (t * (∑ i ∈ range N, Y i) ω)) μ := by
    refine Integrable.of_bound (C := exp (|t| * N)) (by fun_prop) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.2
    have := hSr ω
    calc t * _ ≤ |t * (∑ i ∈ range N, Y i) ω| := le_abs_self _
      _ = |t| * |(∑ i ∈ range N, Y i) ω| := abs_mul _ _
      _ ≤ |t| * N := mul_le_mul_of_nonneg_left (abs_le.2 ⟨this.1, by linarith [this.2]⟩) (abs_nonneg _)
  have h := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ range N, Y i) (-(N * a)) ht hint
  have hmgf : mgf (∑ i ∈ range N, Y i) μ t ≤ exp (N * (p * (exp (-t) - 1))) := by
    rw [hindY.mgf_sum hY]
    calc ∏ i ∈ range N, mgf (Y i) μ t ≤ ∏ _i ∈ range N, exp (p * (exp (-t) - 1)) := by
          gcongr
          · intro i _; exact mgf_nonneg
          rename_i i _
          have := mgf_le (μ := μ) (hX i) (hr i) (hm i) (-t)
          calc mgf (Y i) μ t = mgf (X i) μ (-t) := by
                simp only [mgf, Y]; congr 1; ext ω; ring_nf
            _ ≤ _ := this
      _ = exp (N * (p * (exp (-t) - 1))) := by rw [prod_const, card_range, ← exp_nat_mul]
  have hset : {ω | ∑ i ∈ range N, X i ω ≤ N * a} = {ω | -(N * a) ≤ (∑ i ∈ range N, Y i) ω} := by
    ext ω; simp only [Set.mem_ofPred_eq, Finset.sum_apply, Y, sum_neg_distrib, neg_le_neg_iff]
  rw [hset]
  refine h.trans ?_
  calc exp (-t * -(N * a)) * mgf (∑ i ∈ range N, Y i) μ t
      ≤ exp (-t * -(N * a)) * exp (N * (p * (exp (-t) - 1))) :=
        mul_le_mul_of_nonneg_left hmgf (exp_pos _).le
    _ = exp (-(N * (-t * a - p * (exp (-t) - 1)))) := by rw [← exp_add]; ring_nf

/-- The optimised (Poisson–KL) exponent. -/
noncomputable def poisKL (a p : ℝ) : ℝ := a * log (a / p) - a + p

/-- **Upper tail, optimised:** `p < a` ⇒ `P(Σ X ≥ N a) ≤ exp (−N · poisKL a p)`. -/
theorem upper_opt {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (N : ℕ)
    {a : ℝ} (hp : 0 < p) (hpa : p ≤ a) :
    μ.real {ω | N * a ≤ ∑ i ∈ range N, X i ω} ≤ exp (-(N * poisKL a p)) := by
  have ha : 0 < a := hp.trans_le hpa
  have ht : 0 ≤ log (a / p) := log_nonneg ((one_le_div hp).2 hpa)
  have h := upper_tail hX hind hr hm N a ht
  rw [exp_log (div_pos ha hp), show p * (a / p - 1) = a - p by field_simp] at h
  refine h.trans_eq ?_
  unfold poisKL
  ring_nf

/-- **Lower tail, optimised:** `0 < a ≤ p` ⇒ `P(Σ X ≤ N a) ≤ exp (−N · poisKL a p)`. -/
theorem lower_opt {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (N : ℕ)
    {a : ℝ} (ha : 0 < a) (hap : a ≤ p) :
    μ.real {ω | ∑ i ∈ range N, X i ω ≤ N * a} ≤ exp (-(N * poisKL a p)) := by
  have hp : 0 < p := ha.trans_le hap
  have ht : 0 ≤ log (p / a) := log_nonneg ((one_le_div ha).2 hap)
  have h := lower_tail hX hind hr hm N a ht
  have e1 : exp (-log (p / a)) = a / p := by
    rw [exp_neg, exp_log (div_pos hp ha), inv_div]
  have e2 : log (p / a) = -log (a / p) := by
    rw [← log_inv, inv_div]
  rw [e1, e2] at h
  refine h.trans_eq ?_
  congr 1
  unfold poisKL
  field_simp
  ring

theorem poisKL_alpha {N : ℕ} {a p α : ℝ} (hα : 0 < α) (h : log (1 / α) ≤ N * poisKL a p) :
    exp (-(N * poisKL a p)) ≤ α := by
  calc exp (-(N * poisKL a p)) ≤ exp (-log (1 / α)) := exp_le_exp.2 (by linarith)
    _ = α := by rw [exp_neg, exp_log (by positivity), one_div, inv_inv]

/-- **Calibrated upper test.** -/
theorem upper_alpha {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (N : ℕ)
    {a α : ℝ} (hp : 0 < p) (hpa : p ≤ a) (hα : 0 < α) (h : log (1 / α) ≤ N * poisKL a p) :
    μ.real {ω | N * a ≤ ∑ i ∈ range N, X i ω} ≤ α :=
  (upper_opt hX hind hr hm N hp hpa).trans (poisKL_alpha hα h)

/-- **Calibrated lower test.** -/
theorem lower_alpha {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (N : ℕ)
    {a α : ℝ} (ha : 0 < a) (hap : a ≤ p) (hα : 0 < α) (h : log (1 / α) ≤ N * poisKL a p) :
    μ.real {ω | ∑ i ∈ range N, X i ω ≤ N * a} ≤ α :=
  (lower_opt hX hind hr hm N ha hap).trans (poisKL_alpha hα h)

/-- **Two-sided interval.** With `lo ≤ p ≤ hi` each calibrated at `α`, the count leaves
`(N·lo, N·hi)` with probability at most `2α`. -/
theorem two_sided_alpha {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (N : ℕ)
    {lo hi α : ℝ} (hlo : 0 < lo) (hlop : lo ≤ p) (hphi : p ≤ hi) (hα : 0 < α)
    (h1 : log (1 / α) ≤ N * poisKL lo p) (h2 : log (1 / α) ≤ N * poisKL hi p) :
    μ.real ({ω | ∑ i ∈ range N, X i ω ≤ N * lo} ∪ {ω | N * hi ≤ ∑ i ∈ range N, X i ω}) ≤ 2 * α := by
  calc _ ≤ μ.real {ω | ∑ i ∈ range N, X i ω ≤ N * lo} + μ.real {ω | N * hi ≤ ∑ i ∈ range N, X i ω} :=
        measureReal_union_le _ _
    _ ≤ α + α := add_le_add (lower_alpha hX hind hr hm N hlo hlop hα h1)
        (upper_alpha hX hind hr hm N (hlo.trans_le hlop) hphi hα h2)
    _ = 2 * α := by ring

/-- For `0 < p ≤ a`, `poisKL a p ≥ (a − p)² / (2a)`. Proof: with `v = 1 − p/a ∈ [0,1)`,
`log (a/p) = −log (1 − v) ≥ v + v²/2` (first two terms of the log series). -/
theorem poisKL_ge {a p : ℝ} (hp : 0 < p) (hpa : p ≤ a) : (a - p) ^ 2 / (2 * a) ≤ poisKL a p := by
  have ha : 0 < a := hp.trans_le hpa
  set v := 1 - p / a with hv
  have hpa' : p / a ≤ 1 := (div_le_one ha).2 hpa
  have hv0 : 0 ≤ v := by rw [hv]; linarith
  have hv1 : |v| < 1 := by
    rw [abs_of_nonneg hv0, hv]; linarith [div_pos hp ha]
  have hs := hasSum_pow_div_log_of_abs_lt_one hv1
  have h2 := sum_le_hasSum (range 2) (fun i _ => by positivity) hs
  simp only [sum_range_succ, sum_range_zero] at h2
  norm_num at h2
  have hlog : log (a / p) = -log (1 - v) := by
    rw [hv, sub_sub_cancel, ← log_inv, inv_div]
  have key : v + v ^ 2 / 2 ≤ log (a / p) := by rw [hlog]; linarith
  have hav : a * v = a - p := by rw [hv]; field_simp
  unfold poisKL
  have : (a - p) ^ 2 / (2 * a) = a * (v ^ 2 / 2) := by
    rw [← hav]; field_simp
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left key ha.le]

/-- **Comparison with Hoeffding.** If `0 < p ≤ a ≤ 1/(4c)` with `c > 0`, the Poisson exponent
is at least `c` times Hoeffding's `2(a − p)²`. (`c = 1` at `a ≤ 1/4`; `c = 10` at `a ≤ 0.025`.) -/
theorem beats_hoeffding {a p c : ℝ} (hp : 0 < p) (hpa : p ≤ a) (hc : 0 < c) (ha : a ≤ 1 / (4 * c)) :
    c * (2 * (a - p) ^ 2) ≤ poisKL a p := by
  have ha0 : 0 < a := hp.trans_le hpa
  refine le_trans ?_ (poisKL_ge hp hpa)
  rw [le_div_iff₀ (by positivity)]
  have h4 : 4 * c * a ≤ 1 := by rw [le_div_iff₀ (by positivity)] at ha; linarith
  nlinarith [sq_nonneg (a - p), mul_le_mul_of_nonneg_left h4 (sq_nonneg (a - p))]

end FiveOrgans.PoissonTail
