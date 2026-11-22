import FiveOrgans.Viability
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Stochastic viability: hazard budgets

Each step the agent leaves the viable set `K` with probability `h i ∈ [0, 1]`, given
it was still inside. The probability of staying inside for `n` steps is
`surv h n = ∏_{i<n} (1 - h i)`.

* `surv_ge` — `surv h n ≥ 1 - ∑_{i<n} h i` (union bound, proved by induction).
* `budget_viable` — if the total hazard stays within `ε` at every horizon, then
  `P(stay) ≥ 1 - ε` at every horizon.
* `uniform_split` — over a fixed horizon `N`, a per-step hazard `≤ ε/N` is enough.
* `const_hazard_dies` — any constant hazard `h ∈ (0, 1]` drives survival to `0`. For
  every `ε < 1`, some finite horizon falls below `1 - ε`.
* `geometric_viable` — hazards `ε/2^(i+1)` keep `P(stay) ≥ 1 - ε` forever.

Reading: a fixed error rate cannot give long-run viability, however small it is. Long-run
viability needs a hazard that falls over time (here, a summable one). That is a constraint
on the error-correcting organs (Watcher, Brake): they must drive the per-step failure
rate down over time, not just keep it low.
-/

namespace FiveOrgans.ViabilityStochastic
open Finset

/-- Probability of staying in `K` for `n` steps. -/
def surv (h : ℕ → ℝ) (n : ℕ) : ℝ := ∏ i ∈ range n, (1 - h i)

theorem surv_succ (h : ℕ → ℝ) (n : ℕ) : surv h (n + 1) = surv h n * (1 - h n) := by
  unfold surv; rw [prod_range_succ]

theorem surv_mem (h : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) (n : ℕ) :
    0 ≤ surv h n ∧ surv h n ≤ 1 := by
  induction n with
  | zero => simp [surv]
  | succ n ih =>
    rw [surv_succ]
    obtain ⟨h0, h1⟩ := hh n
    constructor
    · exact mul_nonneg ih.1 (by linarith)
    · nlinarith [ih.1, ih.2]

/-- **Union bound.** -/
theorem surv_ge (h : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) (n : ℕ) :
    1 - ∑ i ∈ range n, h i ≤ surv h n := by
  induction n with
  | zero => simp [surv]
  | succ n ih =>
    rw [surv_succ, sum_range_succ]
    obtain ⟨_, hs1⟩ := surv_mem h hh n
    nlinarith [(hh n).1]

/-- **Hazard budget ⇒ viability at every horizon.** -/
theorem budget_viable (h : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) {ε : ℝ}
    (hb : ∀ n, ∑ i ∈ range n, h i ≤ ε) (n : ℕ) : 1 - ε ≤ surv h n := by
  linarith [surv_ge h hh n, hb n]

/-- Fixed horizon `N`: per-step hazard `≤ ε / N` suffices. -/
theorem uniform_split (h : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) {ε : ℝ} {N : ℕ}
    (hN : 0 < N) (hle : ∀ i, h i ≤ ε / N) : 1 - ε ≤ surv h N := by
  have hs : ∑ i ∈ range N, h i ≤ ε := by
    calc ∑ i ∈ range N, h i ≤ ∑ _i ∈ range N, ε / N := sum_le_sum (fun i _ => hle i)
      _ = ε := by
        rw [sum_const, card_range, nsmul_eq_mul]
        field_simp
  linarith [surv_ge h hh N]

theorem surv_const (c : ℝ) (n : ℕ) : surv (fun _ => c) n = (1 - c) ^ n := by
  unfold surv; rw [prod_const, card_range]

/-- **A constant positive hazard is not viable in the long run.** -/
theorem const_hazard_dies {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {ε : ℝ} (hε : ε < 1) :
    ∃ n, surv (fun _ => c) n < 1 - ε := by
  have ht : Filter.Tendsto (fun n : ℕ => (1 - c) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have hpos : (0 : ℝ) < 1 - ε := by linarith
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hpos)).exists
  exact ⟨n, by rw [surv_const]; exact hn⟩

/-- **A summable (geometric) hazard is viable forever.** -/
theorem geometric_viable {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (n : ℕ) :
    1 - ε ≤ surv (fun i => ε / 2 ^ (i + 1)) n := by
  apply budget_viable
  · intro i
    have : (1 : ℝ) ≤ 2 ^ (i + 1) := one_le_pow₀ (by norm_num)
    exact ⟨by positivity, (div_le_one (by positivity)).mpr (by linarith)⟩
  · intro m
    have key : ∀ m, ∑ i ∈ range m, ε / 2 ^ (i + 1) = ε * (1 - 1 / 2 ^ m) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [sum_range_succ, ih, pow_succ]
        field_simp
        ring
    rw [key]
    have : (0 : ℝ) < 1 / 2 ^ m := by positivity
    nlinarith

/-- `1 - h ≤ e^(-h)`, so survival is at most `exp(-total hazard)`. -/
theorem surv_le_exp (h : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) (n : ℕ) :
    surv h n ≤ Real.exp (-∑ i ∈ range n, h i) := by
  induction n with
  | zero => simp [surv]
  | succ n ih =>
    rw [surv_succ, sum_range_succ, neg_add, Real.exp_add]
    have h1 : 1 - h n ≤ Real.exp (-h n) := by linarith [Real.add_one_le_exp (-h n)]
    have h2 : 0 ≤ 1 - h n := by linarith [(hh n).2]
    exact mul_le_mul ih h1 h2 (Real.exp_pos _).le

/-- **Converse: survival bounded away from 0 forces a bounded total hazard.** If
`P(stay) ≥ c > 0` at every horizon, every partial sum of hazards is at most `-log c`. -/
theorem viable_bounded_hazard (h : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) {c : ℝ}
    (hc : 0 < c) (hs : ∀ n, c ≤ surv h n) (n : ℕ) : ∑ i ∈ range n, h i ≤ -Real.log c := by
  have := (hs n).trans (surv_le_exp h hh n)
  have hl := Real.log_le_log hc this
  rw [Real.log_exp] at hl
  linarith

end FiveOrgans.ViabilityStochastic
