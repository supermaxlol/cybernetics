import FiveOrgans.CoupledPartial
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic

/-!
# Stochastic coupled dynamics: variance, failure-probability bounds, worst case vs average case

Shocks are random: `W i : Ω → ℝ`, pairwise independent, mean zero, square-integrable, with
`Var(W i) ≤ s²`. A configuration responds linearly. Its shock response at time `n` is
`resp a W n = Σ_{t<n} a t · W (n−1−t)`, with `a t = sfac · h t`.

- `var_resp_eq` / `var_resp`: `Var(resp) = Σ aₜ² Var(W) ≤ s² Σ aₜ²`.
- `cheb_resp`: `P(|resp| ≥ c) ≤ s² Σ aₜ² / c²` (Chebyshev).
- `stable_fail_le`: for a **stable** configuration, `P(|shock response at n| ≥ c) ≤ sfac² s² L₁ / c²`
  **uniformly in n**. The union bound `stable_horizon_le` covers a horizon `T` at cost `T × that`.
- `nobrake_var_eq`: under delay without the Brake, `Var` at time `6m` is **exactly**
  `4m · sfac² s²`. It grows linearly and without bound (`nobrake_var_unbounded`). The loop is
  marginally unstable in the mean-square sense: it diffuses like `√n` and does not blow up.
- `worst_vs_average`: in that case the configuration is **never viable in the worst case**
  (`brake_necessary`). Yet at time `6m` its failure probability is `≤ ε` whenever
  `4m · sfac² s² ≤ ε c²`.

  So worst-case necessity does not imply average-case necessity within a finite horizon. The
  crossover horizon scales as `c² / (sfac² s²)`. This is a quantitative prediction for the
  simulations: time-to-failure ∝ `X² / (sfac² s²)`.
- `sustainable_count`: with a shared resource pool `I` and minimum viable cost `c_min > 0`, at
  most `I / c_min` units can be viable at once (resource competition).

Scope.
- Linear dynamics.
- Pairwise-independent shocks (no volatility clustering).
- Chebyshev bounds are loose, but they are distribution-free.
- Nothing here is about a real system.
-/

set_option linter.unusedSectionVars false

namespace FiveOrgans.CoupledStochastic
open MeasureTheory ProbabilityTheory Finset FiveOrgans.Coupled

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Linear response to the random shock sequence `W`. -/
noncomputable def resp (a : ℕ → ℝ) (W : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ range n, a t * W (n - 1 - t) ω

theorem resp_reflect (a : ℕ → ℝ) (W : ℕ → Ω → ℝ) (n : ℕ) :
    resp a W n = ∑ j ∈ range n, fun ω => a (n - 1 - j) * W j ω := by
  funext ω
  simp only [resp, Finset.sum_apply]
  calc ∑ t ∈ range n, a t * W (n - 1 - t) ω
      = ∑ t ∈ range n, (fun j => a (n - 1 - j) * W j ω) (n - 1 - t) :=
        sum_congr rfl fun t ht => by
          rw [mem_range] at ht; simp only; rw [show n - 1 - (n - 1 - t) = t by omega]
    _ = _ := sum_range_reflect (fun j => a (n - 1 - j) * W j ω) n

theorem sq_reflect (a : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range n, a (n - 1 - j) ^ 2 = ∑ t ∈ range n, a t ^ 2 :=
  sum_range_reflect (fun t => a t ^ 2) n

variable {W : ℕ → Ω → ℝ}

theorem memLp_resp (a : ℕ → ℝ) (hm : ∀ i, MemLp (W i) 2 μ) (n : ℕ) :
    MemLp (resp a W n) 2 μ := by
  rw [resp_reflect]
  exact memLp_finsetSum' _ fun j _ => (hm j).const_mul _

theorem var_resp_eq (a : ℕ → ℝ) (hm : ∀ i, MemLp (W i) 2 μ)
    (hind : ∀ i j, i ≠ j → IndepFun (W i) (W j) μ) (n : ℕ) :
    variance (resp a W n) μ = ∑ j ∈ range n, a (n - 1 - j) ^ 2 * variance (W j) μ := by
  rw [resp_reflect, IndepFun.variance_sum (fun j _ => (hm j).const_mul _)]
  · exact sum_congr rfl fun j _ => variance_const_mul _ _ _
  · intro i _ j _ hij
    exact (hind i j hij).comp (measurable_const.mul measurable_id)
      (measurable_const.mul measurable_id)

theorem var_resp (a : ℕ → ℝ) (hm : ∀ i, MemLp (W i) 2 μ)
    (hind : ∀ i j, i ≠ j → IndepFun (W i) (W j) μ) {s2 : ℝ} (hv : ∀ i, variance (W i) μ ≤ s2)
    (n : ℕ) : variance (resp a W n) μ ≤ s2 * ∑ t ∈ range n, a t ^ 2 := by
  rw [var_resp_eq a hm hind, ← sq_reflect, mul_sum]
  exact sum_le_sum fun j _ => by
    rw [mul_comm s2]; exact mul_le_mul_of_nonneg_left (hv j) (sq_nonneg _)

theorem mean_resp (a : ℕ → ℝ) (hm : ∀ i, MemLp (W i) 2 μ) (h0 : ∀ i, μ[W i] = 0) (n : ℕ) :
    μ[resp a W n] = 0 := by
  unfold resp
  rw [integral_finsetSum _ fun t _ => ((hm _).integrable one_le_two).const_mul (a t)]
  simp [integral_const_mul, h0]

/-- **Chebyshev bound** for the shock response. -/
theorem cheb_resp (a : ℕ → ℝ) (hm : ∀ i, MemLp (W i) 2 μ)
    (hind : ∀ i j, i ≠ j → IndepFun (W i) (W j) μ) (h0 : ∀ i, μ[W i] = 0) {s2 : ℝ}
    (hv : ∀ i, variance (W i) μ ≤ s2) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ |resp a W n ω|} ≤ ENNReal.ofReal (s2 * (∑ t ∈ range n, a t ^ 2) / c ^ 2) := by
  have := meas_ge_le_variance_div_sq (memLp_resp a hm n) hc
  rw [mean_resp a hm h0] at this
  simp only [sub_zero] at this
  exact this.trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (var_resp a hm hind hv n) (by positivity)))

/-! ### The coupled configurations -/

variable {C : Cfg} {E : Env}

theorem xC_shock (ω : Ω) (n : ℕ) :
    xC C E (fun j => sfac C E * W j ω) n = resp (fun t => sfac C E * h C E t) W n ω := by
  rw [xC_conv]; unfold resp
  exact sum_congr rfl fun t _ => by ring

theorem h_zero : h C E 0 = 1 := by
  unfold h; split_ifs <;> simp [hd]

theorem sum_sq_le (hs : Stable C E) (n : ℕ) :
    ∑ t ∈ range n, (sfac C E * h C E t) ^ 2 ≤ sfac C E ^ 2 * L1 C := by
  have hle : ∀ t, h C E t ≤ 1 := fun t => h_zero (C := C) (E := E) ▸ h_anti hs (Nat.zero_le t)
  calc ∑ t ∈ range n, (sfac C E * h C E t) ^ 2
      = sfac C E ^ 2 * ∑ t ∈ range n, h C E t ^ 2 := by rw [mul_sum]; simp_rw [mul_pow]
    _ ≤ sfac C E ^ 2 * ∑ t ∈ range n, h C E t := by
        gcongr with t
        have := h_nonneg hs t
        nlinarith [hle t]
    _ ≤ sfac C E ^ 2 * L1 C := by gcongr; exact S_le hs n

/-- **Stable configurations: time-uniform failure-probability bound.** -/
theorem stable_fail_le (hs : Stable C E) (hm : ∀ i, MemLp (W i) 2 μ)
    (hind : ∀ i j, i ≠ j → IndepFun (W i) (W j) μ) (h0 : ∀ i, μ[W i] = 0) {s2 : ℝ}
    (hs2 : 0 ≤ s2) (hv : ∀ i, variance (W i) μ ≤ s2) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ |xC C E (fun j => sfac C E * W j ω) n|} ≤
      ENNReal.ofReal (s2 * (sfac C E ^ 2 * L1 C) / c ^ 2) := by
  simp_rw [xC_shock]
  exact (cheb_resp _ hm hind h0 hv n hc).trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (sum_sq_le hs n) hs2) (by positivity)))

/-- **Horizon union bound.** -/
theorem stable_horizon_le (hs : Stable C E) (hm : ∀ i, MemLp (W i) 2 μ)
    (hind : ∀ i j, i ≠ j → IndepFun (W i) (W j) μ) (h0 : ∀ i, μ[W i] = 0) {s2 : ℝ}
    (hs2 : 0 ≤ s2) (hv : ∀ i, variance (W i) μ ≤ s2) (T : ℕ) {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ n ∈ range T, c ≤ |xC C E (fun j => sfac C E * W j ω) n|} ≤
      T * ENNReal.ofReal (s2 * (sfac C E ^ 2 * L1 C) / c ^ 2) := by
  have : {ω | ∃ n ∈ range T, c ≤ |xC C E (fun j => sfac C E * W j ω) n|} =
      ⋃ n ∈ range T, {ω | c ≤ |xC C E (fun j => sfac C E * W j ω) n|} := by
    ext; simp
  rw [this]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ n ∈ range T, μ {ω | c ≤ |xC C E (fun j => sfac C E * W j ω) n|}
      ≤ ∑ _n ∈ range T, ENNReal.ofReal (s2 * (sfac C E ^ 2 * L1 C) / c ^ 2) :=
        sum_le_sum fun n _ => stable_fail_le hs hm hind h0 hs2 hv n hc
    _ = _ := by simp

/-! ### No Brake under delay: linear variance growth -/

theorem hd1_cases : ∀ t, hd 1 t = 1 ∨ hd 1 t = 0 ∨ hd 1 t = -1
  | 0 => by simp [hd]
  | 1 => by simp [hd]
  | 2 => by norm_num [hd]
  | t + 3 => by rw [hd_one_three]; rcases hd1_cases t with e | e | e <;> simp [e]

theorem hd1_sq (t : ℕ) : hd 1 t ^ 2 = |hd 1 t| := by
  rcases hd1_cases t with e | e | e <;> simp [e]

theorem hd1_sq_sum (m : ℕ) : ∑ t ∈ range (6 * m), hd 1 t ^ 2 = 4 * m := by
  simp_rw [hd1_sq]; exact hd_one_abs_sum m

/-- **Exact variance without the Brake under delay**: `4m · sfac² s²` at time `6m`. -/
theorem nobrake_var_eq (hB : C.B = false) (hd' : E.delay = true) (hm : ∀ i, MemLp (W i) 2 μ)
    (hind : ∀ i j, i ≠ j → IndepFun (W i) (W j) μ) {s2 : ℝ} (hv : ∀ i, variance (W i) μ = s2)
    (m : ℕ) : variance (resp (fun t => sfac C E * h C E t) W (6 * m)) μ =
      4 * m * (sfac C E ^ 2 * s2) := by
  rw [var_resp_eq _ hm hind]
  simp_rw [hv]
  rw [← sum_mul, sq_reflect (fun t => sfac C E * h C E t)]
  simp_rw [h_nB_delay hB hd', mul_pow]
  rw [← mul_sum, hd1_sq_sum]; ring

theorem nobrake_var_unbounded (hE : E.Ok) (hB : C.B = false) (hd' : E.delay = true)
    (hm : ∀ i, MemLp (W i) 2 μ) (hind : ∀ i j, i ≠ j → IndepFun (W i) (W j) μ) {s2 : ℝ}
    (hs2 : 0 < s2) (hv : ∀ i, variance (W i) μ = s2) (V : ℝ) :
    ∃ n, V < variance (resp (fun t => sfac C E * h C E t) W n) μ := by
  have hk : 0 < sfac C E ^ 2 * s2 := by have := sfac_pos (C := C) hE; positivity
  obtain ⟨m, hm'⟩ := exists_nat_gt (V / (4 * (sfac C E ^ 2 * s2)))
  refine ⟨6 * m, ?_⟩
  rw [nobrake_var_eq hB hd' hm hind hv, div_lt_iff₀ (by positivity)] at *
  linarith

/-- **Worst-case necessity is not average-case necessity.** Without the Brake under delay the
configuration is never viable, yet at time `6m` its shock response exceeds `c` with probability
at most `4m·sfac²s²/c²`. -/
theorem worst_vs_average (hB : C.B = false) (hd' : E.delay = true)
    (hm : ∀ i, MemLp (W i) 2 μ) (hind : ∀ i j, i ≠ j → IndepFun (W i) (W j) μ)
    (h0 : ∀ i, μ[W i] = 0) {s2 : ℝ} (hv : ∀ i, variance (W i) μ = s2) (m : ℕ) {c ε : ℝ}
    (hc : 0 < c) (hε : 4 * m * (sfac C E ^ 2 * s2) ≤ ε * c ^ 2) :
    ¬ Viable C E ∧
      μ {ω | c ≤ |xC C E (fun j => sfac C E * W j ω) (6 * m)|} ≤ ENNReal.ofReal ε := by
  refine ⟨brake_necessary hd' hB, ?_⟩
  simp_rw [xC_shock]
  have := meas_ge_le_variance_div_sq (memLp_resp (fun t => sfac C E * h C E t) hm (6 * m)) hc
  rw [mean_resp _ hm h0, nobrake_var_eq hB hd' hm hind hv] at this
  simp only [sub_zero] at this
  refine this.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [div_le_iff₀ (by positivity)]; exact hε

/-! ### Resource competition -/

/-- **Sustainable count.** Units share a pool `I`. If every viable unit costs at least
`cmin > 0`, then at most `I / cmin` units are viable at once. -/
theorem sustainable_count {N : ℕ} (cost : Fin N → ℝ) (viable : Fin N → Prop) [DecidablePred viable]
    {I cmin : ℝ} (hc : 0 < cmin) (hnn : ∀ i, 0 ≤ cost i) (hpool : ∑ i, cost i ≤ I)
    (hmin : ∀ i, viable i → cmin ≤ cost i) :
    ((univ.filter viable).card : ℝ) ≤ I / cmin := by
  rw [le_div_iff₀ hc]
  calc ((univ.filter viable).card : ℝ) * cmin = ∑ _i ∈ univ.filter viable, cmin := by simp
    _ ≤ ∑ i ∈ univ.filter viable, cost i := sum_le_sum fun i hi => hmin i (mem_filter.1 hi).2
    _ ≤ ∑ i, cost i := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun i _ _ => hnn i
    _ ≤ I := hpool

end FiveOrgans.CoupledStochastic
