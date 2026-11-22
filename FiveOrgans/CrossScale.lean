import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic

/-!
# Cross-scale map φ: implementation must preserve interventions, not just behaviour

A *system* has normal dynamics `step` and, for each intervention `i : I` (e.g. "ablate the
memory"), modified dynamics `abl i`. A map `φ : X → Y` from a micro system (a bacterium, a
network) to a macro system (the five-organ agent):

* **behaves like** the macro system if `φ ∘ step = Step ∘ φ` (behaviour only);
* **implements** it if that also holds for every intervention: `φ ∘ abl i = Abl i ∘ φ`.

Results.
* `iterate_comm`, `viable_transfer` — a commuting φ carries whole trajectories, so staying in
  the viable set `K` upstairs is equivalent to staying in `φ⁻¹ K` downstairs.
* `ablation_transfer`, `ablation_kills_iff` — **if φ implements, ablating an organ in the micro
  system has exactly the viability consequences of ablating it in the macro model.** This is
  the licence for any "the bacterium has a memory organ" claim: the necessity theorems
  (`memoryless_fails`, `one_out_kills`, …) then transfer.
* `implements_comp` — implementation composes across scales (cell → organism → agent).
* `orbit_realizes_anything` — **triviality without interventions:** along any non-repeating
  trajectory, some φ makes the micro system reproduce *any* prescribed macro sequence
  (Putnam-style: any system "implements" any behaviour along one run).
* `behaviour_not_enough` — a φ that commutes with the dynamics but not with interventions: the
  macro ablation is fatal, the micro "ablation" is harmless. Behavioural match does not license
  ablation claims.

Scope: deterministic, discrete time, exact commutation, interventions indexed the same at
both scales. Approximate commutation: `CrossScaleApprox`; stochastic systems:
`CrossScaleHazard`, `CrossScaleMarkov`. Whether a real organism
admits such a φ is an empirical claim (EMP?).
-/

namespace FiveOrgans.CrossScale

/-- A system: dynamics plus intervention-modified dynamics. -/
structure Sys (S I : Type*) where
  step : S → S
  abl : I → S → S

variable {X Y Z I : Type*}

/-- Behavioural match only. -/
def Behaves (φ : X → Y) (m : Sys X I) (M : Sys Y I) : Prop :=
  ∀ x, φ (m.step x) = M.step (φ x)

/-- Implementation: behavioural match under the dynamics **and** every intervention. -/
def Implements (φ : X → Y) (m : Sys X I) (M : Sys Y I) : Prop :=
  Behaves φ m M ∧ ∀ i x, φ (m.abl i x) = M.abl i (φ x)

theorem iterate_comm {f : X → X} {g : Y → Y} {φ : X → Y} (h : ∀ x, φ (f x) = g (φ x))
    (n : ℕ) (x : X) : φ (f^[n] x) = g^[n] (φ x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, h]

/-- A commuting map transfers viability step by step. -/
theorem viable_transfer {f : X → X} {g : Y → Y} {φ : X → Y} (h : ∀ x, φ (f x) = g (φ x))
    (K : Set Y) (x : X) (n : ℕ) : f^[n] x ∈ φ ⁻¹' K ↔ g^[n] (φ x) ∈ K := by
  rw [Set.mem_preimage, iterate_comm h]

/-- **Ablation transfers under implementation.** -/
theorem ablation_transfer {φ : X → Y} {m : Sys X I} {M : Sys Y I} (hI : Implements φ m M)
    (i : I) (K : Set Y) (x : X) (n : ℕ) :
    (m.abl i)^[n] x ∈ φ ⁻¹' K ↔ (M.abl i)^[n] (φ x) ∈ K :=
  viable_transfer (hI.2 i) K x n

/-- **An ablation that kills the macroSys agent kills the implementing microSys system (and
conversely), at the same step.** -/
theorem ablation_kills_iff {φ : X → Y} {m : Sys X I} {M : Sys Y I} (hI : Implements φ m M)
    (i : I) (K : Set Y) (x : X) :
    (∃ n, (M.abl i)^[n] (φ x) ∉ K) ↔ ∃ n, (m.abl i)^[n] x ∉ φ ⁻¹' K := by
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, fun h => hn ((ablation_transfer hI i K x n).1 h)⟩
  · rintro ⟨n, hn⟩; exact ⟨n, fun h => hn ((ablation_transfer hI i K x n).2 h)⟩

/-- Normal dynamics transfer too. -/
theorem intact_transfer {φ : X → Y} {m : Sys X I} {M : Sys Y I} (hI : Implements φ m M)
    (K : Set Y) (x : X) (n : ℕ) : m.step^[n] x ∈ φ ⁻¹' K ↔ M.step^[n] (φ x) ∈ K :=
  viable_transfer hI.1 K x n

/-- **Implementation composes across scales.** -/
theorem implements_comp {φ : X → Y} {ψ : Y → Z} {m : Sys X I} {M : Sys Y I} {N : Sys Z I}
    (h₁ : Implements φ m M) (h₂ : Implements ψ M N) : Implements (ψ ∘ φ) m N :=
  ⟨fun x => by simp [Function.comp, h₁.1 x, h₂.1 (φ x)],
   fun i x => by simp [Function.comp, h₁.2 i x, h₂.2 i (φ x)]⟩

/-- **Triviality without interventions:** along a non-repeating orbit, any macroSys sequence is
reproduced by some φ. -/
theorem orbit_realizes_anything {f : X → X} {x₀ : X}
    (hinj : Function.Injective (fun n : ℕ => f^[n] x₀)) (y : ℕ → Y) :
    ∃ φ : X → Y, ∀ n, φ (f^[n] x₀) = y n :=
  ⟨fun x => y (Function.invFun (fun n : ℕ => f^[n] x₀) x),
   fun n => congrArg y (Function.leftInverse_invFun hinj n)⟩

/-- Micro: an "ablation" that changes nothing. -/
def microSys : Sys Bool Unit := ⟨id, fun _ => id⟩
/-- Macro: ablation sends the state out of the viable set `{true}`. -/
def macroSys : Sys Bool Unit := ⟨id, fun _ _ => false⟩

/-- **Behaviour is not enough:** `id` matches the dynamics but not the intervention. The microSys
ablation never leaves the viable set; the macroSys ablation leaves it in one step. -/
theorem behaviour_not_enough :
    Behaves id microSys macroSys ∧ ¬ Implements id microSys macroSys ∧
    (∀ n, (microSys.abl ())^[n] true ∈ (id ⁻¹' {true} : Set Bool)) ∧
    (macroSys.abl ())^[1] (id true) ∉ ({true} : Set Bool) := by
  refine ⟨fun _ => rfl, fun h => ?_, fun n => ?_, ?_⟩
  · have := h.2 () true
    simp [microSys, macroSys] at this
  · simp [microSys]; exact rfl
  · simp [macroSys]; exact fun h => Bool.false_ne_true h

/-- A micro system with a hidden extra bit; its ablation also clears the visible bit. -/
def microFine : Sys (Bool × Bool) Unit := ⟨fun x => (x.1, !x.2), fun _ x => (false, x.2)⟩

/-- **Non-vacuity:** `Prod.fst` implements `macroSys` (dynamics and ablation commute although
the micro system has extra state), so the macro ablation's fatality transfers: the micro
ablation leaves `fst⁻¹{true}` at step 1. -/
theorem implements_instance :
    Implements Prod.fst microFine macroSys ∧
    ∃ n, (microFine.abl ())^[n] (true, true) ∉ (Prod.fst ⁻¹' ({true} : Set Bool)) := by
  have hI : Implements Prod.fst microFine macroSys := ⟨fun _ => rfl, fun _ _ => rfl⟩
  refine ⟨hI, (ablation_kills_iff hI () {true} (true, true)).1 ⟨1, ?_⟩⟩
  simp [macroSys]; exact fun h => Bool.false_ne_true h

end FiveOrgans.CrossScale
