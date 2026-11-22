import Mathlib.Probability.Moments.SubGaussian

/-!
# The row-error bound δ, proved: an ℓ¹ concentration inequality (Weissman type)

`CrossScaleTest` takes as a hypothesis that every row error `rowErr P Ph x ≤ δ`.
`analysis/lumpability_test.py` chose `δ` from the ℓ¹ deviation bound of Weissman et al. (2003).
This module proves that bound (in the slightly weaker `2^m` form) from Mathlib's Hoeffding
inequality.

Setting: `Z 0, Z 1, …` independent draws on a finite state type `α` (`m = card α`) with law `p`
(written `μ[1{Z i = a}] = p a`). The empirical law after `N` draws is `emp Z N ω a`.

* `l1_eq_two_pos` — if two vectors have the same total, their ℓ¹ distance is twice the gain on
  the set where the first exceeds the second. So a large ℓ¹ error forces some set `A` with
  `emp(A) − p(A) ≥ ε/2`.
* `subset_tail` — for a fixed `A`, Hoeffding: `P(emp(A) − p(A) ≥ ε/2) ≤ exp(−N ε²/2)`.
* `l1_tail` — **`P(‖emp − p‖₁ ≥ ε) ≤ 2^m · exp(−N ε²/2)`** (union over the `2^m` subsets).
* `rows_tail` — for one sample sequence per state (any dependence between rows),
  `P(some row has error ≥ δ) ≤ m · 2^m · exp(−N δ²/2)`.
* `delta_solves` — the runner's `δ = √((2/N)(m log 2 + log(m/α)))` makes that bound equal `α`.

Not covered, still an assumption: that a logged Markov chain supplies, for each state, `N`
**i.i.d.** successor draws. The usual justification is the "stack" construction (each state has
its own i.i.d. sequence of successors, read in order), which needs a time-homogeneous Markov
chain. With a data-dependent visit count `N`, an additional union over the possible counts (or a
fixed `N` per state, fixed in advance) is needed. The runner uses the observed visit count.
-/

namespace FiveOrgans.RowConcentration
open MeasureTheory ProbabilityTheory Finset Real
open scoped ENNReal NNReal

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- **ℓ¹ = twice the positive part** when totals agree. -/
theorem l1_eq_two_pos (u v : α → ℝ) (h : ∑ a, u a = ∑ a, v a) :
    ∑ a, |u a - v a| = 2 * ∑ a ∈ univ.filter (fun a => v a < u a), (u a - v a) := by
  have s1 := sum_filter_add_sum_filter_not univ (fun a => v a < u a) (fun a => |u a - v a|)
  have s2 := sum_filter_add_sum_filter_not univ (fun a => v a < u a) (fun a => u a - v a)
  have h0 : ∑ a, (u a - v a) = 0 := by rw [sum_sub_distrib, h, sub_self]
  have e1 : ∑ a ∈ univ.filter (fun a => v a < u a), |u a - v a|
      = ∑ a ∈ univ.filter (fun a => v a < u a), (u a - v a) :=
    sum_congr rfl fun a ha => abs_of_pos (by have := (mem_filter.1 ha).2; linarith)
  have e2 : ∑ a ∈ univ.filter (fun a => ¬ v a < u a), |u a - v a|
      = ∑ a ∈ univ.filter (fun a => ¬ v a < u a), -(u a - v a) :=
    sum_congr rfl fun a ha => abs_of_nonpos (by have := (mem_filter.1 ha).2; push Not at this; linarith)
  rw [e1, e2, sum_neg_distrib] at s1
  linarith

omit [DecidableEq α] in
/-- A large ℓ¹ gap forces a large gain on some subset. -/
theorem l1_witness {u v : α → ℝ} (h : ∑ a, u a = ∑ a, v a) {ε : ℝ}
    (hε : ε ≤ ∑ a, |u a - v a|) : ∃ A ∈ (univ : Finset α).powerset, ε / 2 ≤ ∑ a ∈ A, (u a - v a) :=
  ⟨univ.filter (fun a => v a < u a), mem_powerset.2 (subset_univ _),
    by rw [l1_eq_two_pos u v h] at hε; linarith⟩

/-- Indicator of a finite set. -/
noncomputable def ind (A : Finset α) (x : α) : ℝ := if x ∈ A then 1 else 0

omit [Fintype α] in
theorem ind_eq_sum (A : Finset α) (x : α) : ind A x = ∑ a ∈ A, ind {a} x := by
  unfold ind
  simp only [mem_singleton]
  rw [sum_ite_eq]

theorem ind_univ (x : α) : ∑ a, ind {a} x = 1 := by
  rw [← ind_eq_sum]; simp [ind]

omit [Fintype α] in
theorem ind_mem (A : Finset α) (x : α) : ind A x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold ind; split_ifs <;> simp

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- Empirical frequency of `a` among the first `N` draws. -/
noncomputable def emp (Z : ℕ → Ω → α) (N : ℕ) (ω : Ω) (a : α) : ℝ :=
  (∑ i ∈ range N, ind {a} (Z i ω)) / N

omit [MeasurableSpace Ω] [MeasurableSpace α] [DiscreteMeasurableSpace α] in
theorem emp_sum (Z : ℕ → Ω → α) {N : ℕ} (hN : 0 < N) (ω : Ω) : ∑ a, emp Z N ω a = 1 := by
  unfold emp
  rw [← sum_div, sum_comm]
  simp only [ind_univ, sum_const, card_range, nsmul_eq_mul, mul_one]
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp

omit [Fintype α] [MeasurableSpace Ω] [MeasurableSpace α] [DiscreteMeasurableSpace α] in
theorem emp_gain (Z : ℕ → Ω → α) {N : ℕ} (hN : 0 < N) (p : α → ℝ) (A : Finset α) (ω : Ω) :
    ∑ a ∈ A, (emp Z N ω a - p a) = (∑ i ∈ range N, (ind A (Z i ω) - ∑ a ∈ A, p a)) / N := by
  unfold emp
  have hN' : (N : ℝ) ≠ 0 := by positivity
  rw [sum_sub_distrib, ← sum_div, sum_comm, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  simp_rw [← ind_eq_sum]
  field_simp

omit [Fintype α] in
theorem mean_ind {Y : Ω → α} (hY : Measurable Y) {p : α → ℝ}
    (hlaw : ∀ a, μ[fun ω => ind {a} (Y ω)] = p a) (A : Finset α) :
    μ[fun ω => ind A (Y ω)] = ∑ a ∈ A, p a := by
  simp_rw [ind_eq_sum A]
  rw [integral_finsetSum]
  · exact sum_congr rfl fun a _ => hlaw a
  · intro a _
    exact Integrable.of_mem_Icc 0 1
      (show Measurable (fun ω => ind {a} (Y ω)) from (Measurable.of_discrete (f := ind {a})).comp hY).aemeasurable
      (ae_of_all _ fun ω => ind_mem _ _)

omit [Fintype α] in
/-- **One subset, Hoeffding:** `P(emp(A) − p(A) ≥ ε/2) ≤ exp(−N ε²/2)`. -/
theorem subset_tail {Z : ℕ → Ω → α} (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z μ)
    {p : α → ℝ} (hlaw : ∀ i a, μ[fun ω => ind {a} (Z i ω)] = p a) {N : ℕ} (hN : 0 < N)
    (A : Finset α) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε / 2 ≤ ∑ a ∈ A, (emp Z N ω a - p a)} ≤ exp (-(N * ε ^ 2) / 2) := by
  set X : ℕ → Ω → ℝ := fun i ω => ind A (Z i ω) - ∑ a ∈ A, p a with hX
  have hindX : iIndepFun X μ :=
    hind.comp (fun _ x => ind A x - ∑ a ∈ A, p a) (fun _ => Measurable.of_discrete)
  have hsub : ∀ i < N, HasSubgaussianMGF (X i) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ := by
    intro i _
    have h := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := fun ω => ind A (Z i ω)) (a := 0) (b := 1)
      (show Measurable (fun ω => ind A (Z i ω)) from (Measurable.of_discrete (f := ind A)).comp (hZ i)).aemeasurable
      (ae_of_all _ fun ω => ind_mem _ _)
    rw [mean_ind (hZ i) (hlaw i) A] at h
    exact h
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hH := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hindX hsub (ε := N * ε / 2) (by positivity)
  have hc : (((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = 1 / 4 := by
    push_cast; simp; norm_num
  rw [hc] at hH
  have hexp : -(N * ε / 2) ^ 2 / (2 * N * (1 / 4)) = -(N * ε ^ 2) / 2 := by
    field_simp; ring
  rw [hexp] at hH
  refine le_trans (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)) hH
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [emp_gain Z hN p A ω, le_div_iff₀ hN'] at hω
  simp only [hX]
  linarith

/-- **ℓ¹ concentration (Weissman type):** `P(‖emp − p‖₁ ≥ ε) ≤ 2^m · exp(−N ε²/2)`. -/
theorem l1_tail {Z : ℕ → Ω → α} (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z μ)
    {p : α → ℝ} (hlaw : ∀ i a, μ[fun ω => ind {a} (Z i ω)] = p a) (hp1 : ∑ a, p a = 1)
    {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ a, |emp Z N ω a - p a|}
      ≤ 2 ^ Fintype.card α * exp (-(N * ε ^ 2) / 2) := by
  have hsub : {ω | ε ≤ ∑ a, |emp Z N ω a - p a|}
      ⊆ ⋃ A ∈ (univ : Finset α).powerset, {ω | ε / 2 ≤ ∑ a ∈ A, (emp Z N ω a - p a)} := by
    intro ω hω
    obtain ⟨A, hA, h⟩ := l1_witness (by rw [emp_sum Z hN ω, hp1]) hω
    exact Set.mem_biUnion hA h
  calc μ.real {ω | ε ≤ ∑ a, |emp Z N ω a - p a|}
      ≤ μ.real (⋃ A ∈ (univ : Finset α).powerset,
          {ω | ε / 2 ≤ ∑ a ∈ A, (emp Z N ω a - p a)}) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ A ∈ (univ : Finset α).powerset,
          μ.real {ω | ε / 2 ≤ ∑ a ∈ A, (emp Z N ω a - p a)} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _A ∈ (univ : Finset α).powerset, exp (-(N * ε ^ 2) / 2) :=
          sum_le_sum fun A _ => subset_tail hZ hind hlaw hN A hε
    _ = 2 ^ Fintype.card α * exp (-(N * ε ^ 2) / 2) := by
          rw [sum_const, card_powerset, card_univ, nsmul_eq_mul]; push_cast; ring

/-- **All rows at once:** one i.i.d. sample sequence per state `x` (rows may depend on each other),
`P(∃ x, ‖emp_x − P x‖₁ ≥ δ) ≤ m · 2^m · exp(−N δ²/2)`. -/
theorem rows_tail {Z : α → ℕ → Ω → α} (hZ : ∀ x i, Measurable (Z x i))
    (hind : ∀ x, iIndepFun (Z x) μ) {P : α → α → ℝ}
    (hlaw : ∀ x i a, μ[fun ω => ind {a} (Z x i ω)] = P x a) (hP1 : ∀ x, ∑ a, P x a = 1)
    {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 ≤ δ) :
    μ.real (⋃ x ∈ (univ : Finset α), {ω | δ ≤ ∑ a, |emp (Z x) N ω a - P x a|})
      ≤ Fintype.card α * (2 ^ Fintype.card α * exp (-(N * δ ^ 2) / 2)) := by
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc ∑ x ∈ (univ : Finset α), μ.real {ω | δ ≤ ∑ a, |emp (Z x) N ω a - P x a|}
      ≤ ∑ _x ∈ (univ : Finset α), 2 ^ Fintype.card α * exp (-(N * δ ^ 2) / 2) :=
        sum_le_sum fun x _ => l1_tail (hZ x) (hind x) (hlaw x) (hP1 x) hN hδ
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]

/-- **The runner's δ solves the bound:** `δ² = (2/N)(m log 2 + log(m/α))` gives
`m · 2^m · exp(−N δ²/2) = α`. -/
theorem delta_solves {m N : ℕ} (hm : 0 < m) (hN : 0 < N) {a : ℝ} (ha : 0 < a) {δ : ℝ}
    (hδ : δ ^ 2 = 2 / N * (m * log 2 + log (m / a))) :
    (m : ℝ) * (2 ^ m * exp (-(N * δ ^ 2) / 2)) = a := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have he : -(N * δ ^ 2) / 2 = -(m * log 2) - log (m / a) := by
    rw [hδ]; field_simp; ring
  rw [he, exp_sub, exp_neg, exp_log (by positivity), ← log_rpow (by norm_num : (0 : ℝ) < 2),
    exp_log (by positivity), Real.rpow_natCast]
  field_simp

end FiveOrgans.RowConcentration
