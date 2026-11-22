import FiveOrgans.ViabilityStochastic

/-!
# Stochastic cross-scale map at the hazard level

`CrossScale` and `CrossScaleApprox` map micro **states** to macro states. For stochastic
systems the natural object to match is the per-step **failure probability**: a micro system
with hazards `a i` "stochastically implements" a macro model with hazards `b i` up to mismatch
`|a i - b i|`. (How `a` is computed from a micro process is left abstract; this module needs
only the two hazard sequences.)

* `surv_diff` — survival probabilities differ by at most the **cumulative** hazard mismatch:
  `|surv a n - surv b n| ≤ Σ_{i<n} |a i - b i|`.
* `hazard_transfer_stay` — a macro hazard budget `ε` plus a mismatch budget `δ` give micro
  survival `≥ 1 - ε - δ` at every horizon.
* `hazard_transfer_kill` — a macro death verdict with margin `δ` (`surv b n < 1 - ε - δ`)
  transfers: the micro system's survival is `< 1 - ε` at that step.
* `finite_horizon` — a per-step mismatch `≤ η` costs at most `n η` by step `n`.
* `constant_mismatch_flips` — **the mismatch must be summable for lasting verdicts:** a macro
  model with zero hazard survives with probability 1 forever, while a micro system mismatched
  by any constant `c > 0` per step dies (survival eventually `< 1 - ε` for every `ε < 1`).

Reading: the lifetime ("viable forever") claims of the library transfer to a real stochastic
system only if its failure probabilities match the model's with a **summable** total error.
Matching every step up to a small fixed error is not enough. Scope: hazards given, independent
steps (as in `ViabilityStochastic`). Deriving the hazard of a micro process from a state-level
φ: done in `CrossScaleMarkov` (`sv_approx_lump`).
-/

namespace FiveOrgans.CrossScaleHazard
open Finset FiveOrgans.ViabilityStochastic

/-- **Survival gap ≤ cumulative hazard mismatch.** -/
theorem surv_diff (a b : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (n : ℕ) : |surv a n - surv b n| ≤ ∑ i ∈ range n, |a i - b i| := by
  induction n with
  | zero => simp [surv]
  | succ n ih =>
    rw [surv_succ, surv_succ, sum_range_succ]
    have e : surv a n * (1 - a n) - surv b n * (1 - b n)
        = (surv a n - surv b n) * (1 - a n) + surv b n * (b n - a n) := by ring
    have hb0 := surv_mem b hb n
    rw [e]
    calc |(surv a n - surv b n) * (1 - a n) + surv b n * (b n - a n)|
        ≤ |(surv a n - surv b n) * (1 - a n)| + |surv b n * (b n - a n)| := abs_add_le _ _
      _ = |surv a n - surv b n| * (1 - a n) + surv b n * |a n - b n| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [(ha n).2] : (0 : ℝ) ≤ 1 - a n),
            abs_of_nonneg hb0.1, abs_sub_comm (b n)]
      _ ≤ ∑ i ∈ range n, |a i - b i| + |a n - b n| :=
          add_le_add
            ((mul_le_of_le_one_right (abs_nonneg _) (by linarith [(ha n).1])).trans ih)
            (mul_le_of_le_one_left (abs_nonneg _) hb0.2)

/-- **Viability transfers with a summable mismatch.** -/
theorem hazard_transfer_stay (a b : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) {ε δ : ℝ} (hε : ∀ n, ∑ i ∈ range n, b i ≤ ε)
    (hδ : ∀ n, ∑ i ∈ range n, |a i - b i| ≤ δ) (n : ℕ) : 1 - ε - δ ≤ surv a n := by
  have h1 := budget_viable b hb hε n
  have h2 := (abs_le.1 ((surv_diff a b ha hb n).trans (hδ n))).1
  linarith

/-- **A death verdict with margin transfers.** -/
theorem hazard_transfer_kill (a b : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) {ε δ : ℝ} {n : ℕ}
    (hδ : ∑ i ∈ range n, |a i - b i| ≤ δ) (hdie : surv b n < 1 - ε - δ) :
    surv a n < 1 - ε := by
  have h2 := (abs_le.1 ((surv_diff a b ha hb n).trans hδ)).2
  linarith

/-- **Finite horizon:** a per-step mismatch `≤ η` costs at most `n η`. -/
theorem finite_horizon (a b : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) {η : ℝ} (hη : ∀ i, |a i - b i| ≤ η) (n : ℕ) :
    |surv a n - surv b n| ≤ n * η :=
  (surv_diff a b ha hb n).trans (by
    calc ∑ i ∈ range n, |a i - b i| ≤ ∑ _i ∈ range n, η := sum_le_sum fun i _ => hη i
      _ = n * η := by simp)

/-- **A constant mismatch flips lifetime verdicts:** macro hazard `0` survives forever, micro
hazard `c > 0` (mismatch `c` every step) dies. -/
theorem constant_mismatch_flips {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {ε : ℝ} (hε : ε < 1) :
    (∀ n, surv (fun _ => (0 : ℝ)) n = 1) ∧ ∃ n, surv (fun _ => c) n < 1 - ε :=
  ⟨fun n => by rw [surv_const]; simp, const_hazard_dies hc0 hc1 hε⟩

/-- Non-vacuity: micro hazard `(1/2)^(i+2)` against macro hazard `0` has total
mismatch `≤ 1/2`, so the micro system survives with probability `≥ 1/2` forever. -/
theorem summable_instance (n : ℕ) :
    (1 : ℝ) / 2 ≤ surv (fun i => (1 / 2 : ℝ) ^ (i + 2)) n := by
  have ha : ∀ i, 0 ≤ (1 / 2 : ℝ) ^ (i + 2) ∧ (1 / 2 : ℝ) ^ (i + 2) ≤ 1 :=
    fun i => ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩
  have hδ : ∀ m, ∑ i ∈ range m, |(1 / 2 : ℝ) ^ (i + 2) - 0| ≤ 1 / 2 := by
    intro m
    have hg : ∑ i ∈ range m, (1 / 2 : ℝ) ^ i ≤ 2 := by
      have := sum_geometric_two_le m; simpa [one_div] using this
    calc ∑ i ∈ range m, |(1 / 2 : ℝ) ^ (i + 2) - 0|
        = ∑ i ∈ range m, (1 / 4) * (1 / 2 : ℝ) ^ i := by
          refine sum_congr rfl fun i _ => ?_
          rw [sub_zero, abs_of_nonneg (by positivity)]; ring
      _ = (1 / 4) * ∑ i ∈ range m, (1 / 2 : ℝ) ^ i := by rw [mul_sum]
      _ ≤ 1 / 2 := by linarith
  have := hazard_transfer_stay (fun i => (1 / 2 : ℝ) ^ (i + 2)) (fun _ => 0) ha
    (fun _ => ⟨le_rfl, zero_le_one⟩) (ε := 0) (fun m => by simp) hδ n
  linarith

end FiveOrgans.CrossScaleHazard
