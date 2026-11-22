import FiveOrgans.FiveOrganAgent
import FiveOrgans.WatcherViability

/-!
# The canonical five organs: Skin, Memory (two memories), Spotlight, Brake, Watcher

`FiveOrganAgent` combines five *failure channels*: brake, skin, two-speed, history memory and
spotlight. The Watcher appears there only as something that lowers another organ's hazard. The
conceptual architecture has a different list: Skin, Two Memories, Spotlight, Brake and Watcher.
This module states the capstone for that list.

* **Memory is one organ with two sub-demands.** It must keep the distinctions in history that
  matter (`MemoryRandom`) and keep a fast and a slow trace (`TwoSpeedViability`). The organ's
  per-step hazard is `mergeHz h₁ h₂ = 1 − (1 − h₁)(1 − h₂)`: the organ fails at a step if
  either sub-demand fails. `surv_merge`: the organ's survival is the product of the two
  sub-survivals, so merging changes no joint survival value. It only changes the bookkeeping.
* **The Watcher faces a demand of its own.** The agent's actions carry a residual error
  stream: slips that no other organ's window rules out. The Watcher's job is to catch them.
  Its hazard stream is `watchHz e r i = e · r^i`, the remaining error after review at step `i`.
  - In window (the Watcher improves, `r < 1`): the budget is `e / (1 − r)`
    (`learning_watcher_viable`).
  - Out of window (a static Watcher, `r = 1`, `e > 0`): the hazard is the constant `e`, which
    kills the agent (`static_watcher_still_dies`).

Results:
* `canonical_viable` — **all five canonical organs in their windows ⇒ survival
  `≥ 1 − (c_B|x₀|/(1 − |g − b|) + e/(1 − r))` at every horizon.**
* `memory_part_kills` (either memory sub-demand), `memory_one_rate_kills`,
  `memory_memoryless_kills`, `canon_skin_kills`, `canon_spot_kills`, `canon_brake_kills` and
  `static_watcher_kills` — **any one canonical organ out of its window kills the agent.**
* `canonical_instance` — non-vacuity: every hypothesis holds at once, with survival ≥ 12/25.

Assumptions and scope. Organs combine independently (`JointCorrelated` removes this for the
weakest-link conclusions). The Watcher's residual-error stream is modelled as separate from
the other four organs' hazards. That is a modelling choice: it says the agent makes errors that
no other organ's window prevents. Whether real agents have such a stream, and whether these
five are the right list, is EMP? (`OpenWorld`, `OrganCount`).
-/

namespace FiveOrgans.CanonicalAgent
open Finset FiveOrgans.ViabilityStochastic FiveOrgans.JointViability FiveOrgans.FiveOrganAgent

/-! ### Memory as one organ with two sub-demands -/

/-- Hazard of an organ that fails if either sub-demand fails (sub-demands independent). -/
def mergeHz (h₁ h₂ : ℕ → ℝ) (i : ℕ) : ℝ := 1 - (1 - h₁ i) * (1 - h₂ i)

/-- **Merging is faithful:** the merged organ survives exactly when both sub-demands do. -/
theorem surv_merge (h₁ h₂ : ℕ → ℝ) (n : ℕ) :
    surv (mergeHz h₁ h₂) n = surv h₁ n * surv h₂ n := by
  unfold surv mergeHz
  rw [← prod_mul_distrib]
  simp

theorem mergeHz_mem {h₁ h₂ : ℕ → ℝ} (h1 : ∀ i, 0 ≤ h₁ i ∧ h₁ i ≤ 1)
    (h2 : ∀ i, 0 ≤ h₂ i ∧ h₂ i ≤ 1) (i : ℕ) :
    0 ≤ mergeHz h₁ h₂ i ∧ mergeHz h₁ h₂ i ≤ 1 := by
  obtain ⟨a0, a1⟩ := h1 i
  obtain ⟨b0, b1⟩ := h2 i
  unfold mergeHz
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 a1) (sub_nonneg.2 b1)]

theorem le_mergeHz_left {h₁ h₂ : ℕ → ℝ} (h1 : ∀ i, h₁ i ≤ 1) (h2 : ∀ i, 0 ≤ h₂ i) (i : ℕ) :
    h₁ i ≤ mergeHz h₁ h₂ i := by
  have := h1 i; have := h2 i
  unfold mergeHz; nlinarith

theorem le_mergeHz_right {h₁ h₂ : ℕ → ℝ} (h1 : ∀ i, 0 ≤ h₁ i) (h2 : ∀ i, h₂ i ≤ 1) (i : ℕ) :
    h₂ i ≤ mergeHz h₁ h₂ i := by
  have := h1 i; have := h2 i
  unfold mergeHz; nlinarith

/-! ### The Watcher's own demand: residual error -/

/-- Residual error left after the Watcher's review at step `i`. -/
def watchHz (e r : ℝ) (i : ℕ) : ℝ := e * r ^ i

theorem watchHz_mem {e r : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (i : ℕ) : 0 ≤ watchHz e r i ∧ watchHz e r i ≤ 1 := by
  have h1 : r ^ i ≤ 1 := pow_le_one₀ hr0 hr1
  unfold watchHz
  exact ⟨mul_nonneg he0 (pow_nonneg hr0 i), by nlinarith [pow_nonneg hr0 i]⟩

theorem watch_budget {e r : ℝ} (he0 : 0 ≤ e) (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    ∑ i ∈ range m, watchHz e r i ≤ e / (1 - r) := by
  unfold watchHz
  calc ∑ i ∈ range m, e * r ^ i = e * ∑ i ∈ range m, r ^ i := by rw [mul_sum]
    _ ≤ e * (1 / (1 - r)) := mul_le_mul_of_nonneg_left (BrakeViability.geom_le hr0 hr1 m) he0
    _ = e / (1 - r) := by ring

/-- The canonical layout: 0 skin, 1 memory, 2 spotlight, 3 brake, 4 watcher. -/
def canon (skin mem₁ mem₂ spot brake watch : ℕ → ℝ) : Fin 5 → ℕ → ℝ :=
  ![skin, mergeHz mem₁ mem₂, spot, brake, watch]

/-! ### The capstone -/

/-- **All five canonical organs in their windows ⇒ lasting viability.** -/
theorem canonical_viable
    -- skin
    {cS μ ρ K D s₀ : ℝ} {d : ℕ → ℝ} (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ)
    (hK : μ * K + ρ * D ≤ K) (hd : ∀ n, |d n| ≤ D) (hs : |s₀| ≤ K)
    -- memory, sub-demand 1: two speeds
    {cT σ δ εT : ℝ} {N : ℕ} (hN : 1 ≤ N) (hεT : 0 ≤ εT) (hσ : 0 ≤ σ)
    (hδ : 0 < δ) (hδσ : δ ≤ σ)
    -- memory, sub-demand 2: history
    {H A M : Type*} [Fintype H] {safe : H → A → Prop} {mem : H → M} {π : M → A}
    {cM : ℝ} {μH : H → ℝ} (hsafe : Memory.SafeAgent safe mem π)
    -- spotlight
    {k : ℕ} {cP τ : ℝ} {w val : Fin k → ℝ} (hτ : τ ≤ Spotlight.payoff w val)
    -- brake
    {cB g b x₀ : ℝ} (hcB : 0 ≤ cB) (hw : |g - b| < 1) (hB1 : cB * |x₀| / (1 - |g - b|) ≤ 1)
    -- watcher
    {e r : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hr0 : 0 ≤ r) (hr1 : r < 1) (hW1 : e / (1 - r) ≤ 1)
    (n : ℕ) :
    1 - (cB * |x₀| / (1 - |g - b|) + e / (1 - r)) ≤
      jointSurv 5 (agentHz (canon (SkinViability.hzSkin cS μ ρ K s₀ d)
                                  (TwoSpeedViability.hz cT σ δ εT N 1 (2 * δ / (σ + δ)))
                                  (fun _ => MemoryRandom.rhz cM safe μH (fun h => π (mem h)))
                                  (SpotlightViability.hz cP τ w val)
                                  (BrakeViability.hz cB g b x₀)
                                  (watchHz e r))) n := by
  have z1 := skin_hz_zero (c := cS) hμ hρ hK hd hs
  have z2 := two_speed_hz_zero (c := cT) hN hεT hσ hδ hδσ
  have z3 := memory_hz_zero hsafe cM μH
  have z4 := spot_hz_zero (c := cP) (w := w) hτ
  have zm : ∀ i, mergeHz (TwoSpeedViability.hz cT σ δ εT N 1 (2 * δ / (σ + δ)))
      (fun _ => MemoryRandom.rhz cM safe μH (fun h => π (mem h))) i = 0 := by
    intro i; simp [mergeHz, z2 i, z3]
  have hv : ∀ j i, 0 ≤ (canon (SkinViability.hzSkin cS μ ρ K s₀ d)
      (TwoSpeedViability.hz cT σ δ εT N 1 (2 * δ / (σ + δ)))
      (fun _ => MemoryRandom.rhz cM safe μH (fun h => π (mem h)))
      (SpotlightViability.hz cP τ w val) (BrakeViability.hz cB g b x₀) (watchHz e r)) j i ∧
      (canon (SkinViability.hzSkin cS μ ρ K s₀ d)
      (TwoSpeedViability.hz cT σ δ εT N 1 (2 * δ / (σ + δ)))
      (fun _ => MemoryRandom.rhz cM safe μH (fun h => π (mem h)))
      (SpotlightViability.hz cP τ w val) (BrakeViability.hz cB g b x₀) (watchHz e r)) j i ≤ 1 := by
    intro j i
    fin_cases j
    · simp [canon, z1 i]
    · simp [canon, zm i]
    · simp [canon, z4 i]
    · exact BrakeViability.hz_mem hcB i
    · exact watchHz_mem he0 he1 hr0 hr1.le i
  have hb0 : 0 ≤ cB * |x₀| / (1 - |g - b|) :=
    div_nonneg (mul_nonneg hcB (abs_nonneg _)) (by linarith)
  have hw0 : 0 ≤ e / (1 - r) := div_nonneg he0 (by linarith)
  have h := agent_budget hv (ε := ![0, 0, 0, cB * |x₀| / (1 - |g - b|), e / (1 - r)])
    (fun j => by fin_cases j <;> simp [hb0, hB1, hw0, hW1])
    (fun j m => by
      fin_cases j
      · simp [canon, z1]
      · simp [canon, zm]
      · simp [canon, z4]
      · exact brake_budget hcB hw m
      · exact watch_budget he0 hr0 hr1 m)
    n
  simpa [Fin.sum_univ_five] using h

/-! ### Any one canonical organ out of its window kills the agent -/

section Failures
variable {v : Fin 5 → ℕ → ℝ} (hv : ∀ j i, 0 ≤ v j i ∧ v j i ≤ 1) {ε : ℝ} (hε : ε < 1)
include hv hε

theorem canon_skin_kills {c μ ρ K D : ℝ} (hμ : 0 ≤ μ) (hc : 0 < c)
    (h : K < μ * K + ρ * D) (h0 : v 0 = SkinViability.hzSkin c μ ρ K K (fun _ => D)) :
    ∃ n, jointSurv 5 (agentHz v) n < 1 - ε :=
  agent_one_fails hv 0 hc (fun i => by
    rw [h0]; unfold SkinViability.hzSkin
    simp [lt_of_lt_of_le (SkinViability.steady_push_above hμ h i) (le_abs_self _)]) hε

/-- **Either memory sub-demand failing persistently kills the agent.** -/
theorem memory_part_kills {m₁ m₂ : ℕ → ℝ} (hm₁ : ∀ i, 0 ≤ m₁ i ∧ m₁ i ≤ 1)
    (hm₂ : ∀ i, 0 ≤ m₂ i ∧ m₂ i ≤ 1) (h1 : v 1 = mergeHz m₁ m₂) {h₀ : ℝ} (hpos : 0 < h₀)
    (hlo : (∀ i, h₀ ≤ m₁ i) ∨ (∀ i, h₀ ≤ m₂ i)) :
    ∃ n, jointSurv 5 (agentHz v) n < 1 - ε := by
  refine agent_one_fails hv 1 hpos (fun i => ?_) hε
  rw [h1]
  rcases hlo with h | h
  · exact (h i).trans (le_mergeHz_left (fun i => (hm₁ i).2) (fun i => (hm₂ i).1) i)
  · exact (h i).trans (le_mergeHz_right (fun i => (hm₁ i).1) (fun i => (hm₂ i).2) i)

theorem memory_one_rate_kills {c σ δ εT : ℝ} {N : ℕ} (hσ : 0 ≤ σ) (hδ : 0 < δ) (hδσ : δ ≤ σ)
    (hslow : εT < (1 - 2 * δ / (σ + δ)) ^ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hc : 0 < c) (hc1 : c ≤ 1) {m₂ : ℕ → ℝ} (hm₂ : ∀ i, 0 ≤ m₂ i ∧ m₂ i ≤ 1)
    (h1 : v 1 = mergeHz (TwoSpeedViability.hz c σ δ εT N η η) m₂) :
    ∃ n, jointSurv 5 (agentHz v) n < 1 - ε := by
  have hno : ¬ TwoSpeedViability.Meets σ δ εT N η η :=
    TwoSpeed.single_rate_conflict hσ hδ hδσ hslow hη0 hη1
  have he : ∀ i, TwoSpeedViability.hz c σ δ εT N η η i = c := fun i => by
    simp [TwoSpeedViability.hz, hno]
  exact memory_part_kills hv hε (fun i => by rw [he i]; exact ⟨hc.le, hc1⟩) hm₂ h1 hc
    (Or.inl fun i => (he i).ge)

theorem memory_memoryless_kills {H O A : Type*} [Fintype H] {safe : H → A → Prop}
    {μH : H → ℝ} (hμ : ∀ h, 0 ≤ μH h) (hsum : ∑ h, μH h = 1) {observe : H → O} (π : O → A)
    {h₁ h₂ : H} (hobs : observe h₁ = observe h₂) (hinc : Memory.Incompatible safe h₁ h₂)
    (hp₁ : 0 < μH h₁) (hp₂ : 0 < μH h₂) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {m₁ : ℕ → ℝ} (hm₁ : ∀ i, 0 ≤ m₁ i ∧ m₁ i ≤ 1)
    (h1 : v 1 = mergeHz m₁ (fun _ => MemoryRandom.rhz c safe μH (fun h => π (observe h)))) :
    ∃ n, jointSurv 5 (agentHz v) n < 1 - ε :=
  memory_part_kills hv hε hm₁
    (fun _ => MemoryRandom.rhz_mem hc.le hc1 hμ hsum _) h1 (mul_pos hc (lt_min hp₁ hp₂))
    (Or.inr fun _ => MemoryRandom.memoryless_rhz_ge hc.le hμ π hobs hinc)

theorem canon_spot_kills {k : ℕ} {c τ : ℝ} {w val : Fin k → ℝ}
    (hshort : Spotlight.payoff w val < τ) (hc : 0 < c)
    (h2 : v 2 = SpotlightViability.hz c τ w val) :
    ∃ n, jointSurv 5 (agentHz v) n < 1 - ε :=
  agent_one_fails hv 2 hc (fun i => by
    rw [h2]; simp [SpotlightViability.hz, not_le.mpr hshort]) hε

theorem canon_brake_kills {c g b x₀ : ℝ} (hc : 0 < c) (hx : x₀ ≠ 0) (hw : 1 ≤ |g - b|)
    (h3 : v 3 = BrakeViability.hz c g b x₀) : ∃ n, jointSurv 5 (agentHz v) n < 1 - ε :=
  agent_one_fails hv 3 (lt_min one_pos (mul_pos hc (abs_pos.mpr hx)))
    (fun i => by rw [h3]; exact brake_hz_ge hw hc.le i) hε

/-- **A static Watcher (`r = 1`) with any residual error `e > 0` kills the agent.** -/
theorem static_watcher_kills {e : ℝ} (he : 0 < e) (h4 : v 4 = watchHz e 1) :
    ∃ n, jointSurv 5 (agentHz v) n < 1 - ε :=
  agent_one_fails hv 4 he (fun i => by rw [h4]; simp [watchHz]) hε

end Failures

/-- Non-vacuity: the instance of `five_organs_instance` (skin, two-speed, history memory,
spotlight, brake) plus a Watcher with residual error `1/100` halving each step (budget 1/50).
The canonical agent survives with probability ≥ 12/25 at every horizon. -/
theorem canonical_instance (n : ℕ) :
    (12 : ℝ) / 25 ≤
      jointSurv 5 (agentHz (canon (SkinViability.hzSkin (1 / 100) (1 / 2) 1 2 0 (fun _ => 0))
        (TwoSpeedViability.hz (1 / 100) 1 (1 / 100) (1 / 2) 10 1 (2 * (1 / 100) / (1 + 1 / 100)))
        (fun _ => MemoryRandom.rhz (1 / 100) (fun (h : Bool) (a : Bool) => a = h)
          (fun _ => 1 / 2) (fun h => id (id h)))
        (SpotlightViability.hz (1 / 100) (Spotlight.payoff (Spotlight.uniform 1 2) ![1, 0])
          (Spotlight.uniform 1 2) ![1, 0])
        (BrakeViability.hz (1 / 4) (1 / 2) 0 1)
        (watchHz (1 / 100) (1 / 2)))) n := by
  have h := canonical_viable
    (μ := 1 / 2) (ρ := 1) (K := 2) (D := 1) (s₀ := 0) (d := fun _ => 0) (cS := 1 / 100)
    (by norm_num) (by norm_num) (by norm_num) (fun _ => by norm_num) (by norm_num)
    (cT := 1 / 100) (σ := 1) (δ := 1 / 100) (εT := 1 / 2) (N := 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (safe := fun (h : Bool) (a : Bool) => a = h) (mem := id) (π := id) (cM := 1 / 100)
    (μH := fun _ => 1 / 2) (fun _ => rfl)
    (cP := 1 / 100) (w := Spotlight.uniform 1 2) (val := ![1, 0]) le_rfl
    (cB := 1 / 4) (g := 1 / 2) (b := 0) (x₀ := 1) (by norm_num)
    (by norm_num [abs_of_pos]) (by norm_num [abs_of_pos])
    (e := 1 / 100) (r := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) n
  have : (1 : ℝ) / 4 * |(1 : ℝ)| / (1 - |(1 : ℝ) / 2 - 0|) + 1 / 100 / (1 - 1 / 2) = 13 / 25 := by
    norm_num [abs_of_pos]
  rw [this] at h
  linarith

end FiveOrgans.CanonicalAgent
