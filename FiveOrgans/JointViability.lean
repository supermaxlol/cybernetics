import FiveOrgans.ViabilityStochastic

/-!
# Joint viability: the whole agent survives only if every organ stays within its budget

A composite world with `m` demands (organs) indexed `k < m`. Organ `k` faces hazard
`h k i ∈ [0,1]` at step `i`, **independently** of the others (assumption, EMP?), so the
probability that the whole agent is still viable after `n` steps is

  `jointSurv m h n = ∏_{k<m} surv (h k) n`.

* `joint_le` — the whole is never more viable than any one organ.
* `joint_needs_each` — **necessity**: if the agent's survival stays above `c > 0` forever, then
  *every* organ's cumulative hazard is at most `-log c`. No organ may run out of its window.
* `one_out_kills` — one organ with a hazard bounded below by `h₀ > 0` (e.g. out of window, see
  `BrakeViability`, `SkinViability`, `TwoSpeedViability`, `MemoryViability`,
  `SpotlightViability`, or a static Watcher) drives the **whole** agent's survival to 0,
  however good the others are.
* `all_in_budget` — **sufficiency**: if organ `k`'s cumulative hazard never exceeds `ε k ∈ [0,1]`,
  then the agent survives with probability `≥ 1 - Σ_k ε k` at every horizon.

Reading: viability is a weakest-link property across organs. This is the joint statement the
per-organ links were building towards. It is about *given* hazard streams per organ, and it
is NOT a proof that these five (six) demands are the right or complete list ("exactly five"
remains open), nor that real agents face independent per-organ hazards. `JointCorrelated` drops independence:
the necessity, sufficiency and one-out-kills conclusions survive any coupling.
-/

namespace FiveOrgans.JointViability
open Finset FiveOrgans.ViabilityStochastic

/-- Survival of the whole agent: product over organs. -/
def jointSurv (m : ℕ) (h : ℕ → ℕ → ℝ) (n : ℕ) : ℝ := ∏ k ∈ range m, surv (h k) n

variable {m : ℕ} {h : ℕ → ℕ → ℝ}

/-- Equivalent per-step form: at step `i` the agent survives iff every organ does. -/
theorem joint_eq_steps (n : ℕ) :
    jointSurv m h n = ∏ i ∈ range n, ∏ k ∈ range m, (1 - h k i) := by
  unfold jointSurv surv; exact prod_comm

/-- **The whole is no more viable than any part.** -/
theorem joint_le (hh : ∀ k i, 0 ≤ h k i ∧ h k i ≤ 1) {k : ℕ} (hk : k < m) (n : ℕ) :
    jointSurv m h n ≤ surv (h k) n := by
  unfold jointSurv
  rw [← mul_prod_erase _ _ (mem_range.mpr hk)]
  have h1 : ∏ j ∈ (range m).erase k, surv (h j) n ≤ 1 :=
    prod_le_one₀ (fun j _ => (surv_mem _ (hh j) n).1) (fun j _ => (surv_mem _ (hh j) n).2)
  have h0 := (surv_mem _ (hh k) n).1
  nlinarith

/-- **Necessity: lasting viability forces every organ's hazard to be summable.** -/
theorem joint_needs_each (hh : ∀ k i, 0 ≤ h k i ∧ h k i ≤ 1) {c : ℝ} (hc : 0 < c)
    (hs : ∀ n, c ≤ jointSurv m h n) {k : ℕ} (hk : k < m) (n : ℕ) :
    ∑ i ∈ range n, h k i ≤ -Real.log c :=
  viable_bounded_hazard (h k) (hh k) hc (fun n => (hs n).trans (joint_le hh hk n)) n

/-- **Weakest link: one organ with a persistent hazard kills the whole agent.** -/
theorem one_out_kills (hh : ∀ k i, 0 ≤ h k i ∧ h k i ≤ 1) {k : ℕ} (hk : k < m) {h₀ : ℝ}
    (hpos : 0 < h₀) (hlo : ∀ i, h₀ ≤ h k i) {ε : ℝ} (hε : ε < 1) :
    ∃ n, jointSurv m h n < 1 - ε := by
  have hh₀ : h₀ ≤ 1 := (hlo 0).trans (hh k 0).2
  obtain ⟨n, hn⟩ := const_hazard_dies hpos hh₀ hε
  rw [surv_const] at hn
  refine ⟨n, lt_of_le_of_lt ((joint_le hh hk n).trans ?_) hn⟩
  -- survival under hazards ≥ h₀ is at most (1 - h₀)^n
  clear hn
  induction n with
  | zero => simp [surv]
  | succ n ih =>
    rw [surv_succ, pow_succ]
    have hs := (surv_mem _ (hh k) n).1
    have h2 : 0 ≤ 1 - h k n := by linarith [(hh k n).2]
    exact mul_le_mul ih (by linarith [hlo n]) h2 (hs.trans ih)

/-- **Sufficiency: per-organ budgets add up.** -/
theorem all_in_budget (hh : ∀ k i, 0 ≤ h k i ∧ h k i ≤ 1) {ε : ℕ → ℝ}
    (hε : ∀ k, 0 ≤ ε k ∧ ε k ≤ 1) (hb : ∀ k, k < m → ∀ n, ∑ i ∈ range n, h k i ≤ ε k)
    (n : ℕ) : 1 - ∑ k ∈ range m, ε k ≤ jointSurv m h n := by
  have hstep : ∏ k ∈ range m, (1 - ε k) ≤ jointSurv m h n := by
    unfold jointSurv
    apply prod_le_prod₀
    · intro k _; linarith [(hε k).2]
    · intro k hk
      exact budget_viable (h k) (hh k) (hb k (mem_range.mp hk)) n
  exact (surv_ge ε hε m).trans hstep

/-- Non-vacuity, 2 organs: organ 0 has the geometric hazard `1/(4·2^(i+1))` (budget 1/4), organ 1
the same. Joint survival stays ≥ 1/2 forever. If organ 1 is replaced by a constant 1/100, joint
survival eventually drops below 1/2. -/
theorem joint_instance :
    (∀ n, (1 : ℝ) / 2 ≤ jointSurv 2 (fun _ i => (1 / 4) / 2 ^ (i + 1)) n) ∧
    ∃ n, jointSurv 2 (fun k i => if k = 1 then 1 / 100 else (1 / 4) / 2 ^ (i + 1)) n < 1 / 2 := by
  have hgeo : ∀ i : ℕ, (0 : ℝ) ≤ (1 / 4 : ℝ) / 2 ^ (i + 1) ∧ (1 / 4 : ℝ) / 2 ^ (i + 1) ≤ 1 := by
    intro i
    have : (1 : ℝ) ≤ 2 ^ (i + 1) := one_le_pow₀ (by norm_num)
    exact ⟨by positivity, (div_le_one (by positivity)).mpr (by linarith)⟩
  have hsum : ∀ n, ∑ i ∈ range n, (1 / 4 : ℝ) / 2 ^ (i + 1) ≤ 1 / 4 := by
    intro n
    have key : ∑ i ∈ range n, (1 / 4 : ℝ) / 2 ^ (i + 1) = 1 / 4 * (1 - 1 / 2 ^ n) := by
      induction n with
      | zero => simp
      | succ n ih => rw [sum_range_succ, ih, pow_succ]; field_simp; ring
    rw [key]
    have : (0 : ℝ) < 1 / 2 ^ n := by positivity
    nlinarith
  refine ⟨fun n => ?_, ?_⟩
  · have := all_in_budget (m := 2) (h := fun _ i => (1 / 4) / 2 ^ (i + 1)) (ε := fun _ => 1 / 4)
      (fun _ i => hgeo i) (fun _ => by norm_num) (fun _ _ n => hsum n) n
    simp at this
    linarith
  · have hmix : ∀ k i : ℕ, (0 : ℝ) ≤ (if k = 1 then (1 : ℝ) / 100 else (1 / 4) / 2 ^ (i + 1)) ∧
        (if k = 1 then (1 : ℝ) / 100 else (1 / 4) / 2 ^ (i + 1)) ≤ 1 := by
      intro k i
      by_cases hk : k = 1
      · simp only [hk, ite_true]; norm_num
      · simp only [hk, ite_false]; exact hgeo i
    obtain ⟨n, hn⟩ := one_out_kills
      (h := fun k i => if k = 1 then (1 : ℝ) / 100 else (1 / 4) / 2 ^ (i + 1)) (m := 2)
      hmix (k := 1) (by norm_num)
      (h₀ := 1 / 100) (by norm_num) (fun i => by simp) (ε := 1 / 2) (by norm_num)
    exact ⟨n, by linarith⟩

end FiveOrgans.JointViability
