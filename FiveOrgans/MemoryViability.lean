import FiveOrgans.Memory
import FiveOrgans.ViabilityStochastic

/-!
# Memory × Viability: a memoryless agent can be worn down; a separating memory cannot

Each episode the environment presents a history `e i`. The agent acts through a memory map `mem`
and policy `π`, and fails with hazard `c` whenever its action is unsafe for that history.

* `memoryless_trap` — if two histories look the same (`observe h₁ = observe h₂`) and share no
  safe action, then for every policy `π` acting on the observation, one of the two is unsafe.
* `memoryless_dies` — so an environment that presents only `h₁` or `h₂`, always the one the
  agent gets wrong, makes the hazard the constant `c`, and survival goes to 0.
* `memory_survives` — an agent that is safe after every history (`SafeAgent`) has hazard 0
  in **every** environment, so survival is 1 forever.

Scope: the environment is worst-case (adversarial, or at least never letting the agent off).
Under a random environment the memoryless agent still fails at a positive rate whenever the bad
history has positive probability, but that version is not formalised here. Fifth cross-organ
link. Assumes (EMP?) that unsafe actions carry a fixed hazard.
-/

namespace FiveOrgans.MemoryViability
open FiveOrgans.ViabilityStochastic FiveOrgans.Memory

variable {H O A M : Type*}

open Classical in
/-- Hazard `c` when the action taken after history `e i` is unsafe. -/
noncomputable def hz (c : ℝ) (safe : H → A → Prop) (mem : H → M) (π : M → A) (e : ℕ → H)
    (i : ℕ) : ℝ :=
  if safe (e i) (π (mem (e i))) then 0 else c

/-- **The trap:** a memoryless policy is unsafe after one of two look-alike histories. -/
theorem memoryless_trap {safe : H → A → Prop} {observe : H → O} (π : O → A) {h₁ h₂ : H}
    (hobs : observe h₁ = observe h₂) (hinc : Incompatible safe h₁ h₂) :
    ∃ h, (h = h₁ ∨ h = h₂) ∧ ¬ safe h (π (observe h)) := by
  by_cases hs : safe h₁ (π (observe h₁))
  · exact ⟨h₂, Or.inr rfl, by rw [← hobs]; exact hinc _ hs⟩
  · exact ⟨h₁, Or.inl rfl, hs⟩

/-- **Memoryless ⇒ an environment drawn from `{h₁, h₂}` drives survival to 0.** -/
theorem memoryless_dies {safe : H → A → Prop} {observe : H → O} (π : O → A) {h₁ h₂ : H}
    (hobs : observe h₁ = observe h₂) (hinc : Incompatible safe h₁ h₂)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {ε : ℝ} (hε : ε < 1) :
    ∃ e : ℕ → H, (∀ i, e i = h₁ ∨ e i = h₂) ∧
      ∃ n, surv (hz c safe observe π e) n < 1 - ε := by
  obtain ⟨h, hmem, hbad⟩ := memoryless_trap π hobs hinc
  refine ⟨fun _ => h, fun _ => hmem, ?_⟩
  have : hz c safe observe π (fun _ => h) = fun _ => c := by funext i; simp [hz, hbad]
  rw [this]
  exact const_hazard_dies hc0 hc1 hε

/-- **A safe agent with memory survives every environment.** -/
theorem memory_survives {safe : H → A → Prop} {mem : H → M} {π : M → A}
    (hsafe : SafeAgent safe mem π) (c : ℝ) (e : ℕ → H) (n : ℕ) :
    surv (hz c safe mem π e) n = 1 := by
  have : ∀ i, hz c safe mem π e i = 0 := fun i => by simp [hz, hsafe (e i)]
  unfold surv
  simp [this]

/-- Non-vacuity: two histories `true/false` that look the same, where the only safe action is
to name the history. Every memoryless policy can be worn down; the identity memory survives. -/
theorem memory_instance :
    (∀ π : Unit → Bool, ∃ e : ℕ → Bool,
      ∃ n, surv (hz (1 / 100) (fun h a => a = h) (fun _ => ()) π e) n < 1 / 2) ∧
    ∀ (e : ℕ → Bool) n, surv (hz (1 / 100) (fun h a => a = h) id id e) n = 1 := by
  refine ⟨fun π => ?_, fun e n => memory_survives (fun h => rfl) _ e n⟩
  obtain ⟨e, -, n, hn⟩ := memoryless_dies (safe := fun (h : Bool) (a : Bool) => a = h)
    (observe := fun _ => ()) (h₁ := true) (h₂ := false) π rfl
    (fun a h1 h2 => by rw [h1] at h2; exact Bool.noConfusion h2)
    (c := 1 / 100) (ε := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨e, n, by linarith⟩

end FiveOrgans.MemoryViability
