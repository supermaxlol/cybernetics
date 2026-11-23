import FiveOrgans.CompressionCode

/-!
# Useful compression: one capstone statement

The goal text reached us cut off at "Prove that useful compression". This module does not guess a
single ending. It proves one theorem that covers the natural completions, all relative to a task
`safe : H → A → Prop`.

Call a compression `mem : H → M` **useful** if some policy on it is safe after every history.
Then `useful_compression` states:
1. *Useful = viability-preserving.* `mem` is useful iff some policy on it keeps survival at 1 in
   every environment, for any hazard `0 < c ≤ 1`.
2. *Useful = decision-sufficient.* `mem` is useful iff every memory state admits one action that is
   safe after all the histories it merges.
3. *Useful compression keeps every decision-relevant distinction.* A useful `mem` never merges two
   incompatible histories. Any further merge of such a pair kills (`Compression.forget_kills`).

Companion results proved elsewhere:
- Useful compression need not be predictive: `CompressionInfo.useful_compression_task_relative`.
- The smallest useful memory is the action cover number: `Compression.adequate_fin_iff`.
- Its cost is at least the decision entropy, in both entropy and prefix-code form:
  `CompressionInfo.memory_ge_decision_entropy` and `CompressionCode.safe_code_bound`.
- Approximate compression keeps viability up to a regret budget:
  `Compression.approx_compression_survives` and `CompressionInfo.compression_budget`.
-/

namespace FiveOrgans.UsefulCompression
open FiveOrgans.Memory FiveOrgans.ViabilityStochastic FiveOrgans.MemoryViability
  FiveOrgans.Compression Finset

variable {H A M : Type*}

/-- A compression is useful for a task if some policy on it is always safe. -/
def Useful (safe : H → A → Prop) (mem : H → M) : Prop := ∃ π : M → A, SafeAgent safe mem π

/-- Viability-preserving: some policy keeps survival at 1 in every environment. -/
def Viable (c : ℝ) (safe : H → A → Prop) (mem : H → M) : Prop :=
  ∃ π : M → A, ∀ (e : ℕ → H) (n : ℕ), surv (hz c safe mem π e) n = 1

theorem useful_iff_viable {c : ℝ} (hc0 : 0 < c) (safe : H → A → Prop) (mem : H → M) :
    Useful safe mem ↔ Viable c safe mem := by
  constructor
  · rintro ⟨π, hπ⟩
    exact ⟨π, memory_survives hπ c⟩
  · rintro ⟨π, hπ⟩
    refine ⟨π, fun h => ?_⟩
    by_contra hns
    have := hπ (fun _ => h) 1
    simp [surv, hz, hns] at this
    linarith

/-- **Useful compression.** For a task `safe` and any hazard `c > 0`, the following hold.
(1) Useful ⇔ viability-preserving.
(2) Useful ⇔ every memory state has one action safe after all the histories it merges.
(3) Useful ⇒ incompatible histories are never merged. -/
theorem useful_compression {c : ℝ} (hc0 : 0 < c) (safe : H → A → Prop) (mem : H → M) :
    (Useful safe mem ↔ Viable c safe mem) ∧
    (Useful safe mem ↔ ∀ m : M, ∃ a : A, ∀ h, mem h = m → safe h a) ∧
    (Useful safe mem → ∀ h₁ h₂, Incompatible safe h₁ h₂ → mem h₁ ≠ mem h₂) :=
  ⟨useful_iff_viable hc0 safe mem, adequate_iff safe mem,
    fun ⟨_, hπ⟩ _ _ hinc => separates hπ hinc⟩

/-- Compressing everything to one state is useful iff a single action is safe everywhere. -/
theorem trivial_useful_iff (safe : H → A → Prop) :
    Useful safe (fun _ : H => (0 : Fin 1)) ↔ ∃ a, ∀ h, safe h a := by
  rw [Useful, adequate_iff]
  constructor
  · intro hc; obtain ⟨a, ha⟩ := hc 0; exact ⟨a, fun h => ha h rfl⟩
  · rintro ⟨a, ha⟩ _; exact ⟨a, fun h _ => ha h⟩

/-- **Useful compression, full statement.** Fix a task `safe` in which every history has a safe
action, and a hazard `c > 0`.
(1) For every compression: useful ⇔ viability-preserving, and a useful one never merges
    incompatible histories.
(2) Every compression that merges only decision-equivalent histories is useful, so all
    decision-irrelevant detail may be discarded.
(3) A useful compression with `k` states exists ⇔ `k` actions cover every history (exact minimum).
(4) Total compression (one state) is useful ⇔ one action is safe after every history.
(5) Usefulness is not predictive sufficiency: in a two-history example the predictive laws differ,
    yet one state is useful for one task and not for another.
    (`CompressionInfo.useful_compression_task_relative`.) -/
theorem useful_compression_full [Nonempty A] {c : ℝ} (hc0 : 0 < c) (safe : H → A → Prop)
    (hex : ∀ h, ∃ a, safe h a) :
    (∀ mem : H → M, (Useful safe mem ↔ Viable c safe mem) ∧
      (Useful safe mem → ∀ h₁ h₂, Incompatible safe h₁ h₂ → mem h₁ ≠ mem h₂)) ∧
    (∀ mem : H → M, (∀ h₁ h₂, mem h₁ = mem h₂ → DecEquiv safe h₁ h₂) → Useful safe mem) ∧
    (∀ k : ℕ, (∃ mem : H → Fin k, Useful safe mem) ↔
      ∃ B : Finset A, B.card ≤ k ∧ Covers safe B) ∧
    (Useful safe (fun _ : H => (0 : Fin 1)) ↔ ∃ a, ∀ h, safe h a) :=
  ⟨fun mem => ⟨(useful_compression hc0 safe mem).1, (useful_compression hc0 safe mem).2.2⟩,
    fun mem hmem => factor_adequate safe hex mem hmem,
    fun k => adequate_fin_iff safe k,
    trivial_useful_iff safe⟩

end FiveOrgans.UsefulCompression
