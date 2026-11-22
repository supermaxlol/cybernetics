import FiveOrgans.Spotlight
import FiveOrgans.ViabilityStochastic

/-!
# Spotlight × Viability: aim right and survive, aim wrong and die, spread thin and die

Each episode the agent must earn at least `τ` (its need) from a capacity `C` of attention spread
by an allocation `w` over items worth `v`. Falling short costs hazard `c`.

* `short_dies` — an allocation whose payoff is below `τ` gives hazard `c` every episode, and
  survival goes to 0.
* `spot_survives_if_any` — if **any** feasible allocation meets the need, the spotlight on the
  most valuable item does too (`spot_optimal`), and survives with probability 1. Correct focus
  is the survival-optimal attention policy in this model.
* `demanding_world` — with `τ` set to the best spotlight's payoff, the even spread dies and the
  correct spotlight survives (absence of focus fails).
* `misdirected_world` — with `τ` set to the even spread's payoff, a spotlight on a below-average
  item dies and the even spread survives (focus set wrong is worse than none).

Scope: fixed item values, a fixed need, and a hazard only on shortfall (EMP?). Sixth link. With
`MemoryViability` this gives every organ in the library a survival theorem.
-/

namespace FiveOrgans.SpotlightViability
open FiveOrgans.ViabilityStochastic FiveOrgans.Spotlight

variable {n : ℕ}

open Classical in
/-- Hazard `c` when the payoff falls short of the need `τ`. -/
noncomputable def hz (c τ : ℝ) (w v : Fin n → ℝ) (_ : ℕ) : ℝ :=
  if τ ≤ payoff w v then 0 else c

theorem meets_survives {c τ : ℝ} {w v : Fin n → ℝ} (h : τ ≤ payoff w v) (k : ℕ) :
    surv (hz c τ w v) k = 1 := by
  unfold surv; simp [hz, h]

/-- **Short of the need ⇒ survival → 0.** -/
theorem short_dies {c τ : ℝ} {w v : Fin n → ℝ} (h : payoff w v < τ) (hc0 : 0 < c)
    (hc1 : c ≤ 1) {ε : ℝ} (hε : ε < 1) : ∃ k, surv (hz c τ w v) k < 1 - ε := by
  have : hz c τ w v = fun _ => c := by funext i; simp [hz, not_le.mpr h]
  rw [this]
  exact const_hazard_dies hc0 hc1 hε

/-- **If any feasible allocation survives, the correct spotlight survives.** -/
theorem spot_survives_if_any {c τ C : ℝ} {v w : Fin n → ℝ} {j : Fin n}
    (hmax : ∀ i, v i ≤ v j) (hj : 0 ≤ v j) (hw : Feasible C w) (hτ : τ ≤ payoff w v) (k : ℕ) :
    surv (hz c τ (spot C j) v) k = 1 :=
  meets_survives (hτ.trans (spot_optimal hmax hj hw)) k

/-- **Demanding world: spreading thin dies, the correct spotlight survives.** -/
theorem demanding_world {c C : ℝ} (hC : 0 < C) {v : Fin n → ℝ} {j : Fin n}
    (hmax : ∀ i, v i ≤ v j) {i₀ : Fin n} (hlt : v i₀ < v j) (hc0 : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : ε < 1) :
    (∃ k, surv (hz c (payoff (spot C j) v) (uniform C n) v) k < 1 - ε) ∧
    ∀ k, surv (hz c (payoff (spot C j) v) (spot C j) v) k = 1 :=
  ⟨short_dies (spot_beats_uniform hC hmax hlt) hc0 hc1 hε, meets_survives le_rfl⟩

/-- **Misdirected world: focus on a below-average item dies, the even spread survives.** -/
theorem misdirected_world {c C : ℝ} (hC : 0 < C) {v : Fin n → ℝ} {j : Fin n}
    (hn : (0 : ℝ) < n) (h : v j * n < ∑ i, v i) (hc0 : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : ε < 1) :
    (∃ k, surv (hz c (payoff (uniform C n) v) (spot C j) v) k < 1 - ε) ∧
    ∀ k, surv (hz c (payoff (uniform C n) v) (uniform C n) v) k = 1 :=
  ⟨short_dies (misdirected_spotlight hC hn h) hc0 hc1 hε, meets_survives le_rfl⟩

/-- Non-vacuity: two items worth `1` and `0`, capacity 1, need 1, hazard 1/100. The even spread
(payoff 1/2) is eventually worn below 1/2 survival; the spotlight on item 0 never fails. -/
theorem spotlight_instance :
    (∃ k, surv (hz (1 / 100) (payoff (spot 1 (0 : Fin 2)) ![1, 0]) (uniform 1 2) ![1, 0]) k
      < 1 / 2) ∧
    ∀ k, surv (hz (1 / 100) (payoff (spot 1 (0 : Fin 2)) ![1, 0]) (spot 1 0) ![1, 0]) k = 1 := by
  obtain ⟨h1, h2⟩ := demanding_world (c := 1 / 100) (C := 1) (v := ![1, 0]) (j := 0)
    (i₀ := 1) one_pos (fun i => by fin_cases i <;> simp) (by simp) (by norm_num) (by norm_num)
    (ε := 1 / 2) (by norm_num)
  obtain ⟨k, hk⟩ := h1
  exact ⟨⟨k, by linarith⟩, h2⟩

end FiveOrgans.SpotlightViability
