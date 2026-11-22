import Mathlib.Data.Fintype.Card

/-!
# Two Memories: what a safe agent must remember

Setting. An agent never sees a history `h : H` directly. It keeps a memory state
`mem h : M` and acts by a policy `π : M → A`. `safe h a` says action `a` is safe
after history `h`.

Results.
* `separates`            — a safe agent must give different memory states to
                           incompatible histories.
* `memoryless_fails`     — the pasted proposal's theorem: if two incompatible
                           histories produce the same observation, no
                           observation-only policy is safe.
* `adequate_iff`         — exact characterisation: a memory map admits a safe
                           policy iff every memory state's set of histories
                           shares a common safe action ("compression that keeps
                           what matters").
* `card_le_of_pairwise`  — quantitative lower bound: pairwise-incompatible
                           histories each need their own memory state, so
                           `|S| ≤ |M|`; with `b` bits, `|S| ≤ 2^b`.

Status: pure combinatorics. Nothing here says biological memory has two speeds;
the two-timescale claim needs a separate theorem (see ASSUMPTIONS.md, M3).
-/

namespace FiveOrgans.Memory

variable {H O A M : Type*}

/-- No single action is safe after both histories. -/
def Incompatible (safe : H → A → Prop) (h₁ h₂ : H) : Prop :=
  ∀ a, safe h₁ a → ¬ safe h₂ a

/-- Memory map `mem` with policy `π` acts safely after every history. -/
def SafeAgent (safe : H → A → Prop) (mem : H → M) (π : M → A) : Prop :=
  ∀ h, safe h (π (mem h))

/-- A safe agent separates incompatible histories in memory. -/
theorem separates {safe : H → A → Prop} {mem : H → M} {π : M → A}
    (hsafe : SafeAgent safe mem π) {h₁ h₂ : H}
    (hinc : Incompatible safe h₁ h₂) : mem h₁ ≠ mem h₂ := by
  intro heq
  have s₁ := hsafe h₁
  have s₂ := hsafe h₂
  rw [← heq] at s₂
  exact hinc _ s₁ s₂

/-- Memoryless failure: an observation-only policy cannot be safe when two
incompatible histories look the same. -/
theorem memoryless_fails (safe : H → A → Prop) (observe : H → O) {h₁ h₂ : H}
    (hobs : observe h₁ = observe h₂) (hinc : Incompatible safe h₁ h₂) :
    ¬ ∃ π : O → A, SafeAgent safe observe π := by
  rintro ⟨π, hπ⟩
  exact separates hπ hinc hobs

/-- Exact adequacy: a memory map supports some safe policy iff each memory
state's histories share a safe action. -/
theorem adequate_iff (safe : H → A → Prop) (mem : H → M) :
    (∃ π : M → A, SafeAgent safe mem π) ↔
      ∀ m : M, ∃ a : A, ∀ h, mem h = m → safe h a := by
  constructor
  · rintro ⟨π, hπ⟩ m
    exact ⟨π m, fun h hm => hm ▸ hπ h⟩
  · intro hcov
    choose π hπ using hcov
    exact ⟨π, fun h => hπ (mem h) h rfl⟩

/-- Lower bound: a set of pairwise-incompatible histories needs at least that
many memory states. -/
theorem card_le_of_pairwise [Fintype M] [DecidableEq M]
    {safe : H → A → Prop} {mem : H → M} {π : M → A}
    (hsafe : SafeAgent safe mem π) (S : Finset H)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Incompatible safe x y) :
    S.card ≤ Fintype.card M := by
  have hinj : Set.InjOn mem (S : Set H) := by
    intro x hx y hy hxy
    by_contra hne
    exact separates hsafe (hpair x (Finset.mem_coe.1 hx) y (Finset.mem_coe.1 hy) hne) hxy
  rw [← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_univ _

/-- Bit version: with `b` bits of memory, at most `2^b` pairwise-incompatible
histories can be handled safely. -/
theorem card_le_two_pow {safe : H → A → Prop} {b : ℕ}
    {mem : H → Fin (2 ^ b)} {π : Fin (2 ^ b) → A}
    (hsafe : SafeAgent safe mem π) (S : Finset H)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Incompatible safe x y) :
    S.card ≤ 2 ^ b := by
  simpa using card_le_of_pairwise hsafe S hpair

end FiveOrgans.Memory
