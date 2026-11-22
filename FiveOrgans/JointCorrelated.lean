import FiveOrgans.JointViability
import Mathlib.Tactic.IntervalCases

/-!
# Joint viability without independence: correlated organ hazards

`JointViability` assumes the organs' hazards are independent, so the joint survival is the
product of the marginals. Real organs share shocks. This module drops independence entirely.

Setting: a finite outcome space `Ω` with probabilities `p ω ≥ 0`, `Σ p = 1`. `S k n ω` says
organ `k` is still within its window at time `n` on outcome `ω`. The dependence between organs
is **arbitrary**. `allAlive S m n` is the event that all organs `k < m` are alive.

* `joint_le_marg` — upper Fréchet bound: `P(all alive) ≤ P(organ k alive)` for each `k`.
* `joint_ge` — lower Fréchet (Bonferroni) bound: `P(all alive) ≥ 1 − Σ_k (1 − P(organ k alive))`.
* With marginals `P(S k n) = surv (h k) n` (each organ's own hazard stream, any coupling):
  - `corr_all_in_budget` — **sufficiency survives dependence:** if every organ's cumulative
    hazard is `≤ ε k`, the agent survives with probability `≥ 1 − Σ ε k`.
  - `corr_needs_each` — **necessity survives dependence:** if the agent's survival stays above
    `c > 0`, every organ's cumulative hazard is `≤ −log c`.
  - `corr_one_out_kills` — one organ with a constant hazard `c > 0` kills the agent whatever
    the coupling.
* `dependence_matters` — both Fréchet bounds are attained: two organs, each alive with
  probability `1/2`, can be jointly alive with probability `1/2` (comonotone) or `0`
  (countermonotone). The independent value `1/4` is neither, so the product formula of
  `JointViability` is a modelling choice, not a consequence.

Reading: the weakest-link conclusions (all budgets met is enough, each budget is needed, one
organ out of window kills) do not depend on independence. Only the exact joint value does.
-/

namespace FiveOrgans.JointCorrelated
open Finset FiveOrgans.ViabilityStochastic
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

/-- Probability of an event under weights `p`. -/
noncomputable def P (p : Ω → ℝ) (E : Ω → Prop) : ℝ := ∑ ω, if E ω then p ω else 0

/-- All organs `k < m` alive at time `n`. -/
def allAlive (S : ℕ → ℕ → Ω → Prop) (m n : ℕ) : Ω → Prop := fun ω => ∀ k < m, S k n ω

theorem P_mono {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) {E F : Ω → Prop} (h : ∀ ω, E ω → F ω) :
    P p E ≤ P p F := by
  unfold P
  refine sum_le_sum fun ω _ => ?_
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (h ω h1) h2
  · exact hp ω
  · exact le_rfl

theorem P_and_ge {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1) (E F : Ω → Prop) :
    P p E + P p F - 1 ≤ P p (fun ω => E ω ∧ F ω) := by
  have hpt : ∀ ω, (if E ω then p ω else 0) + (if F ω then p ω else 0) - p ω
      ≤ (if E ω ∧ F ω then p ω else 0) := by
    intro ω
    have := hp ω
    split_ifs <;> first | linarith | (exfalso; tauto)
  have := sum_le_sum fun ω (_ : ω ∈ univ) => hpt ω
  rw [sum_sub_distrib, sum_add_distrib, hp1] at this
  unfold P
  convert this using 3

omit [Fintype Ω] in
theorem allAlive_succ (S : ℕ → ℕ → Ω → Prop) (m n : ℕ) :
    allAlive S (m + 1) n = fun ω => allAlive S m n ω ∧ S m n ω := by
  funext ω
  apply propext
  constructor
  · intro h; exact ⟨fun k hk => h k (by omega), h m (by omega)⟩
  · rintro ⟨h1, h2⟩ k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
    · exact h1 k h
    · subst h; exact h2

/-- Upper Fréchet bound. -/
theorem joint_le_marg {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (S : ℕ → ℕ → Ω → Prop) {m k : ℕ}
    (hk : k < m) (n : ℕ) : P p (allAlive S m n) ≤ P p (S k n) :=
  P_mono hp fun _ h => h k hk

/-- Lower Fréchet (Bonferroni) bound, for any dependence between organs. -/
theorem joint_ge {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (S : ℕ → ℕ → Ω → Prop) (m n : ℕ) :
    1 - ∑ k ∈ range m, (1 - P p (S k n)) ≤ P p (allAlive S m n) := by
  induction m with
  | zero =>
    have hall : ∀ ω, allAlive S 0 n ω := fun ω k hk => absurd hk (Nat.not_lt_zero k)
    simp only [sum_range_zero, sub_zero]
    unfold P
    rw [show (∑ ω, if allAlive S 0 n ω then p ω else 0) = ∑ ω, p ω from
      sum_congr rfl fun ω _ => by simp [hall ω], hp1]
  | succ m ih =>
    rw [allAlive_succ, sum_range_succ]
    have := P_and_ge hp hp1 (allAlive S m n) (S m n)
    linarith

/-- **Sufficiency without independence.** -/
theorem corr_all_in_budget {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    {S : ℕ → ℕ → Ω → Prop} {m : ℕ} {h : ℕ → ℕ → ℝ} (hh : ∀ k i, 0 ≤ h k i ∧ h k i ≤ 1)
    (hmarg : ∀ k, k < m → ∀ n, P p (S k n) = surv (h k) n) {ε : ℕ → ℝ}
    (hb : ∀ k, k < m → ∀ n, ∑ i ∈ range n, h k i ≤ ε k) (n : ℕ) :
    1 - ∑ k ∈ range m, ε k ≤ P p (allAlive S m n) := by
  have h1 := joint_ge hp hp1 S m n
  have h2 : ∑ k ∈ range m, (1 - P p (S k n)) ≤ ∑ k ∈ range m, ε k := by
    refine sum_le_sum fun k hk => ?_
    have hk' := mem_range.1 hk
    rw [hmarg k hk' n]
    have := surv_ge (h k) (hh k) n
    have := hb k hk' n
    linarith
  linarith

/-- **Necessity without independence.** -/
theorem corr_needs_each {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω)
    {S : ℕ → ℕ → Ω → Prop} {m : ℕ} {h : ℕ → ℕ → ℝ} (hh : ∀ k i, 0 ≤ h k i ∧ h k i ≤ 1)
    (hmarg : ∀ k, k < m → ∀ n, P p (S k n) = surv (h k) n) {c : ℝ} (hc : 0 < c)
    (hs : ∀ n, c ≤ P p (allAlive S m n)) {k : ℕ} (hk : k < m) (n : ℕ) :
    ∑ i ∈ range n, h k i ≤ -Real.log c :=
  viable_bounded_hazard (h k) (hh k) hc
    (fun n => (hs n).trans ((joint_le_marg hp S hk n).trans_eq (hmarg k hk n))) n

/-- **One organ out of window kills, whatever the coupling.** -/
theorem corr_one_out_kills {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω)
    {S : ℕ → ℕ → Ω → Prop} {m : ℕ} {h : ℕ → ℕ → ℝ}
    (hmarg : ∀ k, k < m → ∀ n, P p (S k n) = surv (h k) n) {k : ℕ} (hk : k < m)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hconst : ∀ i, h k i = c) {ε : ℝ} (hε : ε < 1) :
    ∃ n, P p (allAlive S m n) < 1 - ε := by
  obtain ⟨n, hn⟩ := const_hazard_dies hc0 hc1 hε
  have he : h k = fun _ => c := funext hconst
  refine ⟨n, lt_of_le_of_lt (joint_le_marg hp S hk n) ?_⟩
  rw [hmarg k hk n, he]; exact hn

omit [Fintype Ω] in
theorem allAlive_two (S : ℕ → ℕ → Ω → Prop) (n : ℕ) :
    allAlive S 2 n = fun ω => S 0 n ω ∧ S 1 n ω := by
  rw [allAlive_succ, allAlive_succ]
  funext ω
  apply propext
  constructor
  · rintro ⟨⟨_, h0⟩, h1⟩; exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩; exact ⟨⟨fun k hk => absurd hk (Nat.not_lt_zero k), h0⟩, h1⟩

/-- **Both Fréchet bounds are attained**, so the independent product `1/4` is not forced. -/
theorem dependence_matters :
    let p : Fin 2 → ℝ := fun _ => 1 / 2
    let Sco : ℕ → ℕ → Fin 2 → Prop := fun _ _ ω => ω = 0
    let Santi : ℕ → ℕ → Fin 2 → Prop := fun k _ ω => ω = if k = 0 then 0 else 1
    (P p (Sco 0 0) = 1 / 2 ∧ P p (Sco 1 0) = 1 / 2 ∧ P p (allAlive Sco 2 0) = 1 / 2) ∧
    (P p (Santi 0 0) = 1 / 2 ∧ P p (Santi 1 0) = 1 / 2 ∧ P p (allAlive Santi 2 0) = 0) := by
  intro p Sco Santi
  simp only [allAlive_two]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp [P, p, Sco, Santi, Fin.sum_univ_two]

end FiveOrgans.JointCorrelated
