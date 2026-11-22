import FiveOrgans.CrossScaleTest

/-!
# Markov order as lumpability

A second-order chain on `X` (next state depends on the previous **and** current state) is a
first-order chain on pairs `(previous, current)`: the *lift*. This module proves:

* `lift_blk` — the lift's probability of landing in the block "current state = c" from `(a, b)`
  is `P2 a b c`.
* `lift_rowsum`, `lift_nonneg` — the lift is a (sub)stochastic kernel when `P2` is.
* `markov_iff_lumpable` — **the previous state is irrelevant (`P2 a b c = Q b c`) iff the lift
  is lumpable onto `Q` through `Prod.snd`.** So "is the chain first-order Markov?" is itself a
  lumpability question, one level down.
* `sv_markov` — if the previous state is irrelevant, survival of the lifted chain equals survival
  of the first-order chain `Q` from the current state, at every horizon.
* `markov_check_refutes` — **the Markov check is an instance of the lumpability test:** two
  pairs with the same current state whose estimated block rows differ by more than `2δ`
  (row errors `≤ δ`) refute first-order Markov for every `Q`. This is
  `CrossScaleTest.split_refutes_lumpable` applied to the lift.
* `mem_not_markov` — a two-state witness: with memory, no first-order chain on the current
  state reproduces even one-step survival.
* `order2_of_order1` — every first-order kernel lifts to a lumpable second-order one, so the
  hierarchy is consistent.

Reading. The empirical lesson "find a Markov micro level before testing φ" has a precise form:
lift the history until the projection that forgets the oldest coordinate is lumpable. The
statistical tests for lumpability then also test the Markov order. What is not here: higher
orders by iteration (the lift of a lift is the same construction with `X × X` for `X`), and any
claim that a real system has finite order.
-/

namespace FiveOrgans.MarkovOrder
open Finset Classical FiveOrgans.CrossScaleMarkov FiveOrgans.CrossScaleTest

variable {X : Type*} [Fintype X]

/-- The pair lift: `(a, b) → (b', c)` has probability `P2 a b c` if `b' = b`, else `0`. -/
noncomputable def lift (P2 : X → X → X → ℝ) (ab bc : X × X) : ℝ :=
  if bc.1 = ab.2 then P2 ab.1 ab.2 bc.2 else 0

theorem lift_blk (P2 : X → X → X → ℝ) (a b c : X) :
    ∑ x' ∈ univ.filter (fun x' : X × X => x'.2 = c), lift P2 (a, b) x' = P2 a b c := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [lift]

omit [Fintype X] in
theorem lift_nonneg {P2 : X → X → X → ℝ} (h : ∀ a b c, 0 ≤ P2 a b c) (ab bc : X × X) :
    0 ≤ lift P2 ab bc := by
  unfold lift; split_ifs
  · exact h _ _ _
  · exact le_rfl

theorem lift_rowsum (P2 : X → X → X → ℝ) (a b : X) :
    ∑ x', lift P2 (a, b) x' = ∑ c, P2 a b c := by
  rw [Fintype.sum_prod_type]
  simp [lift]

/-- **Markov order as lumpability.** -/
theorem markov_iff_lumpable (P2 : X → X → X → ℝ) (Q : X → X → ℝ) :
    Lumpable Prod.snd (lift P2) Q ↔ ∀ a b c, P2 a b c = Q b c := by
  constructor
  · intro h a b c
    have := h (a, b) c
    rwa [lift_blk] at this
  · rintro h ⟨a, b⟩ c
    rw [lift_blk]; exact h a b c

/-- **Survival transfer when the previous state is irrelevant.** -/
theorem sv_markov {P2 : X → X → X → ℝ} {Q : X → X → ℝ} (h : ∀ a b c, P2 a b c = Q b c)
    (K : Set X) (n : ℕ) (a b : X) :
    sv (lift P2) (Prod.snd ⁻¹' K) n (a, b) = sv Q K n b :=
  sv_lump ((markov_iff_lumpable P2 Q).2 h) K n (a, b)

/-- **The Markov check is a lumpability test on the lift.** -/
theorem markov_check_refutes {P2 : X → X → X → ℝ} {Ph : X × X → X × X → ℝ} {δ : ℝ}
    {a₁ a₂ b : X} (h1 : rowErr (lift P2) Ph (a₁, b) ≤ δ) (h2 : rowErr (lift P2) Ph (a₂, b) ≤ δ)
    (hgap : 2 * δ < ∑ c, |blk Prod.snd Ph (a₁, b) c - blk Prod.snd Ph (a₂, b) c|) :
    ¬ ∃ Q : X → X → ℝ, ∀ a b c, P2 a b c = Q b c := by
  rintro ⟨Q, hQ⟩
  exact split_refutes_lumpable (φ := Prod.snd) (x₁ := (a₁, b)) (x₂ := (a₂, b)) rfl h1 h2 hgap ⟨Q, (markov_iff_lumpable P2 Q).2 hQ⟩

/-- First-order kernels lift to lumpable second-order ones. -/
theorem order2_of_order1 (P : X → X → ℝ) :
    Lumpable Prod.snd (lift fun _ b c => P b c) P :=
  (markov_iff_lumpable _ P).2 fun _ _ _ => rfl

/-- The true lift's block rows are the second-order probabilities themselves, so a gap between
`P2 a₁ b ·` and `P2 a₂ b ·` is exactly a within-block split of the lift. -/
theorem lift_blk_eq (P2 : X → X → X → ℝ) (a b c : X) :
    blk Prod.snd (lift P2) (a, b) c = P2 a b c :=
  lift_blk P2 a b c

/-- Memory witness on `Bool` (`true` = alive). From an alive state, the chain stays alive with
probability `1` if the previous state was alive and `1/2` if it was not. -/
noncomputable def P2mem : Bool → Bool → Bool → ℝ := fun a b c =>
  if b then (if c then (if a then 1 else 1 / 2) else (if a then 0 else 1 / 2)) else
    (if c then 0 else 1)

theorem mem_sv_split :
    sv (lift P2mem) (Prod.snd ⁻¹' {true}) 1 (true, true) = 1 ∧
    sv (lift P2mem) (Prod.snd ⁻¹' {true}) 1 (false, true) = 1 / 2 := by
  constructor <;> simp [sv, lift, P2mem, Fintype.sum_prod_type]

/-- **Memory defeats every first-order description:** no first-order chain on the current state
reproduces the one-step survival of `P2mem`, even though both pairs have the same current state. -/
theorem mem_not_markov :
    ¬ ∃ Q : Bool → Bool → ℝ, ∀ x : Bool × Bool,
      sv (lift P2mem) (Prod.snd ⁻¹' {true}) 1 x = sv Q {true} 1 x.2 :=
  no_chain_of_split (φ := Prod.snd) (x₁ := (true, true)) (x₂ := (false, true)) rfl (by
    rw [mem_sv_split.1, mem_sv_split.2]; norm_num)

end FiveOrgans.MarkovOrder
