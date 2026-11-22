import FiveOrgans.JointViability
import FiveOrgans.BrakeViability
import FiveOrgans.SkinViability
import FiveOrgans.TwoSpeedViability
import FiveOrgans.MemoryRandom
import FiveOrgans.SpotlightViability

/-!
# Capstone: the five-organ agent

`JointViability` is stated for abstract hazard streams. Here the five concrete organ hazards from
the per-organ viability modules are plugged in, one stream per organ, combined independently
(assumption, EMP?):

  0 brake      `BrakeViability.hz`      (hazard ∝ deviation, `min 1 (c·|x_n|)`)
  1 skin       `SkinViability.hzSkin`   (hazard `c` on leaving the band `[-K, K]`)
  2 two-speed  `TwoSpeedViability.hz`   (hazard `c` if catch-the-change or low-ripple is unmet)
  3 memory     `MemoryRandom.rhz`       (random environment, hazard `c` on an unsafe action)
  4 spotlight  `SpotlightViability.hz`  (hazard `c` when the payoff falls short of the need)

* `agent_budget`, `agent_one_fails` — the joint theorem specialised to five streams.
* `five_organs_viable` — **all five in their windows ⇒ the agent survives with probability
  `≥ 1 - c_B·|x₀| / (1 - |g - b|)` at every horizon.** Only the brake contributes, because the
  other four in-window hazards are exactly 0.
* `brake_failure_kills`, `skin_failure_kills`, `one_rate_kills`, `memoryless_kills`,
  `short_focus_kills` — **any one organ out of its window kills the agent, whatever the other
  four do.**

Scope. This puts the per-organ results into one statement. It does not show that these five are
the right or complete list of demands ("exactly five" is not a theorem; `OpenWorld` reclassifies it EMP?). It does not show that real
organ hazards are independent; `JointCorrelated` shows the weakest-link conclusions do not
need independence. The Watcher is not a sixth stream here: in this library it lowers
an organ's hazard (`WatcherViability`) rather than facing a demand of its own.
-/

namespace FiveOrgans.FiveOrganAgent
open Finset FiveOrgans.ViabilityStochastic FiveOrgans.JointViability

/-- Five hazard streams laid out as organs `0..4`; indices `≥ 5` carry no hazard. -/
def agentHz (v : Fin 5 → ℕ → ℝ) (k i : ℕ) : ℝ := if hk : k < 5 then v ⟨k, hk⟩ i else 0

theorem agentHz_mem {v : Fin 5 → ℕ → ℝ} (hv : ∀ j i, 0 ≤ v j i ∧ v j i ≤ 1) (k i : ℕ) :
    0 ≤ agentHz v k i ∧ agentHz v k i ≤ 1 := by
  unfold agentHz; split_ifs with hk
  · exact hv _ i
  · norm_num

/-- **Five-organ budget theorem.** -/
theorem agent_budget {v : Fin 5 → ℕ → ℝ} (hv : ∀ j i, 0 ≤ v j i ∧ v j i ≤ 1)
    {ε : Fin 5 → ℝ} (hε : ∀ j, 0 ≤ ε j ∧ ε j ≤ 1)
    (hb : ∀ j n, ∑ i ∈ range n, v j i ≤ ε j) (n : ℕ) :
    1 - ∑ j, ε j ≤ jointSurv 5 (agentHz v) n := by
  set ε' : ℕ → ℝ := fun k => if hk : k < 5 then ε ⟨k, hk⟩ else 0
  have h := all_in_budget (m := 5) (h := agentHz v) (ε := ε') (agentHz_mem hv)
    (fun k => by
      simp only [ε']; split_ifs with hk
      · exact hε _
      · norm_num)
    (fun k hk n => by simpa [agentHz, ε', hk] using hb ⟨k, hk⟩ n) n
  have hs : ∑ k ∈ range 5, ε' k = ∑ j, ε j := by
    simp [ε', Finset.sum_range_succ, Fin.sum_univ_five]
  linarith

/-- **Any one organ with a persistent hazard kills the five-organ agent.** -/
theorem agent_one_fails {v : Fin 5 → ℕ → ℝ} (hv : ∀ j i, 0 ≤ v j i ∧ v j i ≤ 1) (j : Fin 5)
    {h₀ : ℝ} (hpos : 0 < h₀) (hlo : ∀ i, h₀ ≤ v j i) {ε : ℝ} (hε : ε < 1) :
    ∃ n, jointSurv 5 (agentHz v) n < 1 - ε :=
  one_out_kills (agentHz_mem hv) (k := j.val) j.isLt hpos
    (fun i => by simpa [agentHz, j.isLt] using hlo i) hε

/-! ### Per-organ facts in the form the joint theorem needs -/

/-- Brake in window: cumulative hazard `≤ c|x₀| / (1 - |g - b|)`. -/
theorem brake_budget {c g b x₀ : ℝ} (hc : 0 ≤ c) (hw : |g - b| < 1) (m : ℕ) :
    ∑ i ∈ range m, BrakeViability.hz c g b x₀ i ≤ c * |x₀| / (1 - |g - b|) := by
  calc ∑ i ∈ range m, BrakeViability.hz c g b x₀ i
      ≤ ∑ i ∈ range m, c * |x₀| * |g - b| ^ i := by
        apply sum_le_sum; intro i _
        refine (min_le_right _ _).trans (le_of_eq ?_)
        rw [BrakeViability.abs_traj]; ring
    _ = c * |x₀| * ∑ i ∈ range m, |g - b| ^ i := by rw [mul_sum]
    _ ≤ c * |x₀| * (1 / (1 - |g - b|)) :=
        mul_le_mul_of_nonneg_left (BrakeViability.geom_le (abs_nonneg _) hw m)
          (mul_nonneg hc (abs_nonneg _))
    _ = c * |x₀| / (1 - |g - b|) := by ring

/-- Brake out of window: hazard `≥ min 1 (c|x₀|)` at every step. -/
theorem brake_hz_ge {c g b x₀ : ℝ} (hw : 1 ≤ |g - b|) (hc : 0 ≤ c) (i : ℕ) :
    min 1 (c * |x₀|) ≤ BrakeViability.hz c g b x₀ i := by
  unfold BrakeViability.hz
  apply min_le_min_left
  rw [BrakeViability.abs_traj]
  have : |x₀| ≤ |g - b| ^ i * |x₀| := le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hw)
  exact mul_le_mul_of_nonneg_left this hc

theorem skin_hz_zero {c μ ρ K D s₀ : ℝ} {d : ℕ → ℝ} (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ)
    (h : μ * K + ρ * D ≤ K) (hd : ∀ n, |d n| ≤ D) (hs : |s₀| ≤ K) (i : ℕ) :
    SkinViability.hzSkin c μ ρ K s₀ d i = 0 := by
  unfold SkinViability.hzSkin
  simp [not_lt.mpr (Skin.skin_invariant hμ hρ h hd hs (i + 1))]

theorem two_speed_hz_zero {c σ δ ε : ℝ} {N : ℕ} (hN : 1 ≤ N) (hε : 0 ≤ ε) (hσ : 0 ≤ σ)
    (hδ : 0 < δ) (hδσ : δ ≤ σ) (i : ℕ) :
    TwoSpeedViability.hz c σ δ ε N 1 (2 * δ / (σ + δ)) i = 0 := by
  have hyes : TwoSpeedViability.Meets σ δ ε N 1 (2 * δ / (σ + δ)) :=
    TwoSpeed.two_rates_suffice hN hε hσ hδ hδσ
  simp [TwoSpeedViability.hz, hyes]

theorem memory_hz_zero {H A M : Type*} [Fintype H] {safe : H → A → Prop} {mem : H → M}
    {π : M → A} (hsafe : Memory.SafeAgent safe mem π) (c : ℝ) (μ : H → ℝ) :
    MemoryRandom.rhz c safe μ (fun h => π (mem h)) = 0 := by
  classical
  unfold MemoryRandom.rhz; simp [hsafe _]

theorem spot_hz_zero {n : ℕ} {c τ : ℝ} {w v : Fin n → ℝ} (h : τ ≤ Spotlight.payoff w v)
    (i : ℕ) : SpotlightViability.hz c τ w v i = 0 := by
  simp [SpotlightViability.hz, h]

/-! ### The capstone -/

/-- **All five organs in their windows ⇒ lasting viability with an explicit bound.** -/
theorem five_organs_viable
    -- brake
    {cB g b x₀ : ℝ} (hcB : 0 ≤ cB) (hw : |g - b| < 1) (hB1 : cB * |x₀| / (1 - |g - b|) ≤ 1)
    -- skin
    {cS μ ρ K D s₀ : ℝ} {d : ℕ → ℝ} (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ)
    (hK : μ * K + ρ * D ≤ K) (hd : ∀ n, |d n| ≤ D) (hs : |s₀| ≤ K)
    -- two-speed
    {cT σ δ εT : ℝ} {N : ℕ} (hN : 1 ≤ N) (hεT : 0 ≤ εT) (hσ : 0 ≤ σ)
    (hδ : 0 < δ) (hδσ : δ ≤ σ)
    -- memory
    {H A M : Type*} [Fintype H] {safe : H → A → Prop} {mem : H → M} {π : M → A}
    {cM : ℝ} {μH : H → ℝ} (hsafe : Memory.SafeAgent safe mem π)
    -- spotlight
    {k : ℕ} {cP τ : ℝ} {w val : Fin k → ℝ} (hτ : τ ≤ Spotlight.payoff w val) (n : ℕ) :
    1 - cB * |x₀| / (1 - |g - b|) ≤
      jointSurv 5 (agentHz ![BrakeViability.hz cB g b x₀,
                             SkinViability.hzSkin cS μ ρ K s₀ d,
                             TwoSpeedViability.hz cT σ δ εT N 1 (2 * δ / (σ + δ)),
                             fun _ => MemoryRandom.rhz cM safe μH (fun h => π (mem h)),
                             SpotlightViability.hz cP τ w val]) n := by
  have z1 := skin_hz_zero (c := cS) hμ hρ hK hd hs
  have z2 := two_speed_hz_zero (c := cT) hN hεT hσ hδ hδσ
  have z3 := memory_hz_zero hsafe cM μH
  have z4 := spot_hz_zero (c := cP) (w := w) hτ
  have hv : ∀ j i, 0 ≤ (![BrakeViability.hz cB g b x₀, SkinViability.hzSkin cS μ ρ K s₀ d,
      TwoSpeedViability.hz cT σ δ εT N 1 (2 * δ / (σ + δ)),
      fun _ => MemoryRandom.rhz cM safe μH (fun h => π (mem h)),
      SpotlightViability.hz cP τ w val] : Fin 5 → ℕ → ℝ) j i ∧
      (![BrakeViability.hz cB g b x₀, SkinViability.hzSkin cS μ ρ K s₀ d,
      TwoSpeedViability.hz cT σ δ εT N 1 (2 * δ / (σ + δ)),
      fun _ => MemoryRandom.rhz cM safe μH (fun h => π (mem h)),
      SpotlightViability.hz cP τ w val] : Fin 5 → ℕ → ℝ) j i ≤ 1 := by
    intro j i
    fin_cases j
    · exact BrakeViability.hz_mem hcB i
    · simp [z1 i]
    · simp [z2 i]
    · simp [z3]
    · simp [z4 i]
  have hb0 : 0 ≤ cB * |x₀| / (1 - |g - b|) :=
    div_nonneg (mul_nonneg hcB (abs_nonneg _)) (by linarith)
  have h := agent_budget hv (ε := ![cB * |x₀| / (1 - |g - b|), 0, 0, 0, 0])
    (fun j => by fin_cases j <;> simp [hb0, hB1])
    (fun j m => by
      fin_cases j
      · exact brake_budget hcB hw m
      · simp [z1]
      · simp [z2]
      · simp [z3]
      · simp [z4])
    n
  simpa [Fin.sum_univ_five] using h

/-! ### Any one organ out of its window kills the agent, whatever the others do -/

section Failures
variable {v : Fin 5 → ℕ → ℝ} (hv : ∀ j i, 0 ≤ v j i ∧ v j i ≤ 1) {ε : ℝ} (hε : ε < 1)
include hv hε

theorem brake_failure_kills {c g b x₀ : ℝ} (hc : 0 < c) (hx : x₀ ≠ 0) (hw : 1 ≤ |g - b|)
    (h0 : v 0 = BrakeViability.hz c g b x₀) : ∃ n, jointSurv 5 (agentHz v) n < 1 - ε :=
  agent_one_fails hv 0 (lt_min one_pos (mul_pos hc (abs_pos.mpr hx)))
    (fun i => by rw [h0]; exact brake_hz_ge hw hc.le i) hε

theorem skin_failure_kills {c μ ρ K D : ℝ} (hμ : 0 ≤ μ) (hc : 0 < c)
    (h : K < μ * K + ρ * D) (h1 : v 1 = SkinViability.hzSkin c μ ρ K K (fun _ => D)) :
    ∃ n, jointSurv 5 (agentHz v) n < 1 - ε :=
  agent_one_fails hv 1 hc (fun i => by
    rw [h1]; unfold SkinViability.hzSkin
    simp [lt_of_lt_of_le (SkinViability.steady_push_above hμ h i) (le_abs_self _)]) hε

theorem one_rate_kills {c σ δ εT : ℝ} {N : ℕ} (hσ : 0 ≤ σ) (hδ : 0 < δ) (hδσ : δ ≤ σ)
    (hslow : εT < (1 - 2 * δ / (σ + δ)) ^ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hc : 0 < c)
    (h2 : v 2 = TwoSpeedViability.hz c σ δ εT N η η) :
    ∃ n, jointSurv 5 (agentHz v) n < 1 - ε :=
  agent_one_fails hv 2 hc (fun i => by
    have hno : ¬ TwoSpeedViability.Meets σ δ εT N η η :=
      TwoSpeed.single_rate_conflict hσ hδ hδσ hslow hη0 hη1
    rw [h2]; simp [TwoSpeedViability.hz, hno]) hε

theorem memoryless_kills {H O A : Type*} [Fintype H] {safe : H → A → Prop} {μH : H → ℝ}
    (hμ : ∀ h, 0 ≤ μH h) {observe : H → O} (π : O → A) {h₁ h₂ : H}
    (hobs : observe h₁ = observe h₂) (hinc : Memory.Incompatible safe h₁ h₂)
    (hp₁ : 0 < μH h₁) (hp₂ : 0 < μH h₂) {c : ℝ} (hc : 0 < c)
    (h3 : v 3 = fun _ => MemoryRandom.rhz c safe μH (fun h => π (observe h))) :
    ∃ n, jointSurv 5 (agentHz v) n < 1 - ε :=
  agent_one_fails hv 3 (mul_pos hc (lt_min hp₁ hp₂)) (fun i => by
    rw [h3]; exact MemoryRandom.memoryless_rhz_ge hc.le hμ π hobs hinc) hε

theorem short_focus_kills {k : ℕ} {c τ : ℝ} {w val : Fin k → ℝ}
    (hshort : Spotlight.payoff w val < τ) (hc : 0 < c)
    (h4 : v 4 = SpotlightViability.hz c τ w val) :
    ∃ n, jointSurv 5 (agentHz v) n < 1 - ε :=
  agent_one_fails hv 4 hc (fun i => by
    rw [h4]; simp [SpotlightViability.hz, not_le.mpr hshort]) hε

end Failures

end FiveOrgans.FiveOrganAgent

namespace FiveOrgans.FiveOrganAgent
open FiveOrgans.JointViability

/-- Non-vacuity: every hypothesis of `five_organs_viable` holds at once. Brake `g - b = 1/2`,
`x₀ = 1`, `c_B = 1/4` (budget 1/2); skin `μ = 1/2, ρ = 1, K = 2, D = 1`, start 0, no
disturbance; two-speed `σ = 1, δ = 1/100, N = 10, ε = 1/2`; memory: Bool histories, identity
memory, uniform μ; spotlight: need equal to the allocation's own payoff. The agent survives
with probability ≥ 1/2 at every horizon. -/
theorem five_organs_instance (n : ℕ) :
    (1 : ℝ) / 2 ≤
      jointSurv 5 (agentHz ![BrakeViability.hz (1 / 4) (1 / 2) 0 1,
                             SkinViability.hzSkin (1 / 100) (1 / 2) 1 2 0 (fun _ => 0),
                             TwoSpeedViability.hz (1 / 100) 1 (1 / 100) (1 / 2) 10 1
                               (2 * (1 / 100) / (1 + 1 / 100)),
                             fun _ => MemoryRandom.rhz (1 / 100) (fun (h : Bool) (a : Bool) => a = h)
                               (fun _ => 1 / 2) (fun h => id (id h)),
                             SpotlightViability.hz (1 / 100)
                               (Spotlight.payoff (Spotlight.uniform 1 2) ![1, 0])
                               (Spotlight.uniform 1 2) ![1, 0]]) n := by
  have h := five_organs_viable (cB := 1 / 4) (g := 1 / 2) (b := 0) (x₀ := 1) (by norm_num)
    (by norm_num [abs_of_pos]) (by norm_num [abs_of_pos])
    (μ := 1 / 2) (ρ := 1) (K := 2) (D := 1) (s₀ := 0) (d := fun _ => 0) (cS := 1 / 100)
    (by norm_num) (by norm_num) (by norm_num) (fun _ => by norm_num) (by norm_num)
    (cT := 1 / 100) (σ := 1) (δ := 1 / 100) (εT := 1 / 2) (N := 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (safe := fun (h : Bool) (a : Bool) => a = h) (mem := id) (π := id) (cM := 1 / 100)
    (μH := fun _ => 1 / 2) (fun _ => rfl)
    (cP := 1 / 100) (w := Spotlight.uniform 1 2) (val := ![1, 0]) le_rfl n
  have : (1 : ℝ) / 4 * |(1 : ℝ)| / (1 - |(1 : ℝ) / 2 - 0|) = 1 / 2 := by
    norm_num [abs_of_pos]
  rw [this] at h
  linarith

end FiveOrgans.FiveOrganAgent
