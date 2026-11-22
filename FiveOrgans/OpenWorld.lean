import FiveOrgans.JointViability

/-!
# "Exactly five": completeness is relative to a world class, and fails in an open one

`ASSUMPTIONS.md` lists "exactly five organs" (completeness) as OPEN. This module settles what
can be settled mathematically.

* `open_world_incomplete` — **no finite organ list is complete for an open world class.**
  Take any `m` demands with any hazards. Add one more demand that the agent does not meet
  (constant hazard `h₀ > 0`). The agent with all `m` organs in budget then dies. So
  "exactly five" cannot be a theorem about all possible worlds; it can only hold relative to a
  stipulated class of demands.
* `closed_world_complete` — **relative completeness:** within a world class whose demands are
  exactly the listed `m`, meeting each one's budget is sufficient (`all_in_budget`) and every
  one is necessary (`joint_needs_each`). For the five modelled demands this is what
  `FiveOrganAgent` instantiates.
* `organ_not_universal` — **no organ is necessary in every world:** if a demand carries no
  hazard, the agent survives with probability 1 whatever that organ does.

Reading: "exactly five" is not a claim the maths can prove. It is a claim about which demands
the real worlds of interest contain. That is EMP?, and the empirical question is whether some
sixth demand carries a non-summable hazard for real agents. The gap is closed by showing it is
not a theorem; it is reclassified as EMP?.
-/

namespace FiveOrgans.OpenWorld
open Finset FiveOrgans.ViabilityStochastic FiveOrgans.JointViability

/-- Extend a hazard family by one unmet demand with constant hazard `h₀`. -/
noncomputable def extend (m : ℕ) (h : ℕ → ℕ → ℝ) (h₀ : ℝ) : ℕ → ℕ → ℝ :=
  fun k => if k < m then h k else fun _ => h₀

/-- **No finite organ list is complete for an open world class.** -/
theorem open_world_incomplete (m : ℕ) (h : ℕ → ℕ → ℝ) (hh : ∀ k i, 0 ≤ h k i ∧ h k i ≤ 1)
    {h₀ : ℝ} (hpos : 0 < h₀) (h1 : h₀ ≤ 1) {ε : ℝ} (hε : ε < 1) :
    (∀ k, k < m → extend m h h₀ k = h k) ∧ ∃ n, jointSurv (m + 1) (extend m h h₀) n < 1 - ε := by
  refine ⟨fun k hk => by simp [extend, hk], ?_⟩
  have hh' : ∀ k i, 0 ≤ extend m h h₀ k i ∧ extend m h h₀ k i ≤ 1 := by
    intro k i; unfold extend; split_ifs
    · exact hh k i
    · exact ⟨hpos.le, h1⟩
  exact one_out_kills hh' (Nat.lt_succ_self m) hpos (fun i => by simp [extend]) hε

/-- **Relative completeness:** in a closed world with exactly `m` demands, all budgets met is
sufficient and each bounded budget is necessary. -/
theorem closed_world_complete {m : ℕ} {h : ℕ → ℕ → ℝ} (hh : ∀ k i, 0 ≤ h k i ∧ h k i ≤ 1)
    {ε : ℕ → ℝ} (hε : ∀ k, 0 ≤ ε k ∧ ε k ≤ 1)
    (hb : ∀ k, k < m → ∀ n, ∑ i ∈ range n, h k i ≤ ε k) :
    (∀ n, 1 - ∑ k ∈ range m, ε k ≤ jointSurv m h n) ∧
    ∀ {c : ℝ}, 0 < c → (∀ n, c ≤ jointSurv m h n) →
      ∀ k, k < m → ∀ n, ∑ i ∈ range n, h k i ≤ -Real.log c :=
  ⟨all_in_budget hh hε hb, fun hc hs k hk n => joint_needs_each hh hc hs hk n⟩

/-- **No organ is necessary in every world:** a demand with zero hazard never kills. -/
theorem organ_not_universal (n : ℕ) : surv (fun _ => (0 : ℝ)) n = 1 := by
  rw [surv_const]; simp

end FiveOrgans.OpenWorld
