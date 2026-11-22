import FiveOrgans.MemoryViability

/-!
# Memory × Viability in a random environment

`MemoryViability` showed the memoryless agent dies only against a worst-case environment. Here
the environment is **random**: at each step a history `h` is drawn independently from a fixed
distribution `μ` on a finite set of histories `H` (assumption, EMP?). An agent acting by
`act : H → A` fails with probability `c` whenever its action is unsafe for the drawn history, so
its per-step failure probability is the constant

  `rhz c safe μ act = c · Σ_h μ(h) · [act h unsafe after h]`,

and, by independence across steps, its survival after `n` steps is `surv (fun _ => rhz) n
= (1 - rhz)^n`.

* `memoryless_rhz_ge` — if two look-alike histories with no common safe action **both** occur
  with positive probability, then every memoryless policy has per-step failure probability at
  least `c · min(μ h₁, μ h₂) > 0`.
* `memoryless_dies_random` — so its survival goes to 0, with the explicit rate
  `surv ≤ (1 - c · min(μ h₁, μ h₂))^n` (`memoryless_rate`).
* `memory_safe_random` — a safe agent with memory has per-step failure probability 0 and
  survives with probability 1 under **every** distribution.

This removes the worst-case restriction of `MemoryViability`. The trap no longer needs an
adversary: any environment that sometimes shows each of two look-alike histories wears down a
memoryless agent.
-/

namespace FiveOrgans.MemoryRandom
open Finset FiveOrgans.ViabilityStochastic FiveOrgans.Memory

variable {H O A M : Type*} [Fintype H]

open Classical in
/-- Per-step failure probability under a random history drawn from `μ`. -/
noncomputable def rhz (c : ℝ) (safe : H → A → Prop) (μ : H → ℝ) (act : H → A) : ℝ :=
  c * ∑ h, μ h * (if safe h (act h) then 0 else 1)

theorem rhz_mem {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {safe : H → A → Prop} {μ : H → ℝ}
    (hμ : ∀ h, 0 ≤ μ h) (hsum : ∑ h, μ h = 1) (act : H → A) :
    0 ≤ rhz c safe μ act ∧ rhz c safe μ act ≤ 1 := by
  classical
  have hs0 : 0 ≤ ∑ h, μ h * (if safe h (act h) then (0 : ℝ) else 1) :=
    sum_nonneg fun h _ => mul_nonneg (hμ h) (by split_ifs <;> norm_num)
  have hs1 : ∑ h, μ h * (if safe h (act h) then (0 : ℝ) else 1) ≤ 1 := by
    rw [← hsum]
    exact sum_le_sum fun h _ => by
      split_ifs <;> nlinarith [hμ h]
  unfold rhz
  exact ⟨mul_nonneg hc0 hs0, by nlinarith⟩

/-- **The trap has positive probability:** a memoryless policy fails at rate at least
`c · min(μ h₁, μ h₂)`. -/
theorem memoryless_rhz_ge {c : ℝ} (hc0 : 0 ≤ c) {safe : H → A → Prop} {μ : H → ℝ}
    (hμ : ∀ h, 0 ≤ μ h) {observe : H → O} (π : O → A) {h₁ h₂ : H}
    (hobs : observe h₁ = observe h₂) (hinc : Incompatible safe h₁ h₂) :
    c * min (μ h₁) (μ h₂) ≤ rhz c safe μ (fun h => π (observe h)) := by
  classical
  obtain ⟨h, hmem, hbad⟩ := MemoryViability.memoryless_trap π hobs hinc
  have hmin : min (μ h₁) (μ h₂) ≤ μ h := by
    rcases hmem with rfl | rfl
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hterm : μ h ≤ ∑ h', μ h' * (if safe h' (π (observe h')) then (0 : ℝ) else 1) := by
    have := single_le_sum (f := fun h' => μ h' * (if safe h' (π (observe h')) then (0 : ℝ) else 1))
      (fun h' _ => mul_nonneg (hμ h') (by split_ifs <;> norm_num)) (mem_univ h)
    simpa [hbad] using this
  unfold rhz
  exact mul_le_mul_of_nonneg_left (hmin.trans hterm) hc0

/-- Survival under a per-step hazard of at least `h₀` is at most `(1 - h₀)^n`. -/
theorem surv_le_of_ge {r h₀ : ℝ} (hr : r ≤ 1) (hlo : h₀ ≤ r) (n : ℕ) :
    surv (fun _ => r) n ≤ (1 - h₀) ^ n := by
  rw [surv_const]
  have : 0 ≤ 1 - r := by linarith
  exact pow_le_pow_left₀ this (by linarith) n

/-- **Explicit rate for the memoryless agent.** -/
theorem memoryless_rate {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {safe : H → A → Prop}
    {μ : H → ℝ} (hμ : ∀ h, 0 ≤ μ h) (hsum : ∑ h, μ h = 1) {observe : H → O} (π : O → A)
    {h₁ h₂ : H} (hobs : observe h₁ = observe h₂) (hinc : Incompatible safe h₁ h₂) (n : ℕ) :
    surv (fun _ => rhz c safe μ (fun h => π (observe h))) n
      ≤ (1 - c * min (μ h₁) (μ h₂)) ^ n :=
  surv_le_of_ge (rhz_mem hc0 hc1 hμ hsum _).2 (memoryless_rhz_ge hc0 hμ π hobs hinc) n

/-- **Random environment: a memoryless agent is worn down.** -/
theorem memoryless_dies_random {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {safe : H → A → Prop}
    {μ : H → ℝ} (hμ : ∀ h, 0 ≤ μ h) (hsum : ∑ h, μ h = 1) {observe : H → O} (π : O → A)
    {h₁ h₂ : H} (hobs : observe h₁ = observe h₂) (hinc : Incompatible safe h₁ h₂)
    (hp₁ : 0 < μ h₁) (hp₂ : 0 < μ h₂) {ε : ℝ} (hε : ε < 1) :
    ∃ n, surv (fun _ => rhz c safe μ (fun h => π (observe h))) n < 1 - ε := by
  set h₀ := c * min (μ h₁) (μ h₂)
  have hpos : 0 < h₀ := mul_pos hc0 (lt_min hp₁ hp₂)
  have hge := memoryless_rhz_ge hc0.le hμ π hobs hinc
  have hr := rhz_mem (safe := safe) hc0.le hc1 hμ hsum (fun h => π (observe h))
  obtain ⟨n, hn⟩ := const_hazard_dies hpos (hge.trans hr.2) hε
  rw [surv_const] at hn
  exact ⟨n, lt_of_le_of_lt (surv_le_of_ge hr.2 hge n) hn⟩

/-- **A safe agent with memory survives every random environment.** -/
theorem memory_safe_random {safe : H → A → Prop} {mem : H → M} {π : M → A}
    (hsafe : SafeAgent safe mem π) (c : ℝ) (μ : H → ℝ) (n : ℕ) :
    surv (fun _ => rhz c safe μ (fun h => π (mem h))) n = 1 := by
  classical
  have : rhz c safe μ (fun h => π (mem h)) = 0 := by
    unfold rhz; simp [hsafe _]
  rw [this, surv_const]; simp

/-- Non-vacuity: histories `true/false` equally likely and indistinguishable to a memoryless
agent, where the only safe action names the history. Every memoryless policy fails at rate
at least `1/200` per step (`c = 1/100`), and its survival eventually drops below 1/2. The
identity memory never fails. -/
theorem random_instance :
    (∀ π : Unit → Bool,
      (1 : ℝ) / 200 ≤ rhz (1 / 100) (fun h a => a = h) (fun _ => 1 / 2) (fun _ => π ()) ∧
      ∃ n, surv (fun _ => rhz (1 / 100) (fun (h : Bool) (a : Bool) => a = h) (fun _ => 1 / 2)
        (fun _ => π ())) n < 1 / 2) ∧
    ∀ n, surv (fun _ => rhz (1 / 100) (fun (h : Bool) (a : Bool) => a = h) (fun _ => 1 / 2)
      (fun h => id (id h))) n = 1 := by
  have hinc : Incompatible (fun (h : Bool) (a : Bool) => a = h) true false :=
    fun a h1 h2 => by rw [h1] at h2; exact Bool.noConfusion h2
  have hμ : ∀ h : Bool, (0 : ℝ) ≤ (fun _ => 1 / 2) h := fun _ => by norm_num
  have hsum : ∑ h : Bool, (fun _ => (1 : ℝ) / 2) h = 1 := by simp
  refine ⟨fun π => ⟨?_, ?_⟩, fun n => memory_safe_random (mem := id) (π := id)
    (fun h => rfl) _ _ n⟩
  · have := memoryless_rhz_ge (c := 1 / 100) (by norm_num) hμ (observe := fun _ => ()) π
      (h₁ := true) (h₂ := false) rfl hinc
    simp only [min_self] at this
    linarith
  · obtain ⟨n, hn⟩ := memoryless_dies_random (c := 1 / 100) (by norm_num) (by norm_num) hμ hsum
      (observe := fun _ => ()) π (h₁ := true) (h₂ := false) rfl hinc (by norm_num)
      (by norm_num) (ε := 1 / 2) (by norm_num)
    exact ⟨n, by linarith⟩

end FiveOrgans.MemoryRandom
