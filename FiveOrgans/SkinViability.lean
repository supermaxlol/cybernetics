import FiveOrgans.Skin
import FiveOrgans.ViabilityStochastic

/-!
# Skin × Viability: the skin window is exactly the line between "never breached" and "eventually dies"

The internal state follows the Skin model `s (n+1) = μ s n + ρ d n` with disturbances
`|d n| ≤ D`. The agent faces hazard `c` at step `n` if the state after the step leaves the
tolerance band, `K < |s (n+1)|`, and no hazard otherwise.

* `skin_in_window_safe` — if `μK + ρD ≤ K`, then for every admissible disturbance and every start
  inside the band, the hazard is identically 0 and `P(stay) = 1` at every horizon.
* `skin_out_of_window_dies` — if `K < μK + ρD` (with `μ, ρ ≥ 0`), the steady worst-case
  disturbance `d ≡ D` from `s₀ = K` keeps the state above `K` at every step. So with `c > 0`
  survival goes to 0.

Unlike the Brake and Watcher links, the boundary here is sharp and the guarantee inside is
total (survival 1, not just bounded below). That is because the Skin bounds the worst case,
not the average. Third cross-organ link. Assumes hazard only outside the band (EMP?).
-/

namespace FiveOrgans.SkinViability
open FiveOrgans.ViabilityStochastic

/-- Hazard `c` whenever the next state leaves the band `[-K, K]`. -/
noncomputable def hzSkin (c μ ρ K s₀ : ℝ) (d : ℕ → ℝ) (n : ℕ) : ℝ :=
  if K < |Skin.traj μ ρ s₀ d (n + 1)| then c else 0

/-- **Inside the window: never breached, survival 1 forever.** -/
theorem skin_in_window_safe {c μ ρ K D s₀ : ℝ} {d : ℕ → ℝ} (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ)
    (h : μ * K + ρ * D ≤ K) (hd : ∀ n, |d n| ≤ D) (hs : |s₀| ≤ K) (n : ℕ) :
    surv (hzSkin c μ ρ K s₀ d) n = 1 := by
  have h0 : ∀ i, hzSkin c μ ρ K s₀ d i = 0 := by
    intro i
    unfold hzSkin
    simp [not_lt.mpr (Skin.skin_invariant hμ hρ h hd hs (i + 1))]
  unfold surv
  simp [h0]

/-- Under the steady worst-case push, the state stays above `K`. -/
theorem steady_push_above {μ ρ K D : ℝ} (hμ : 0 ≤ μ) (h : K < μ * K + ρ * D) (n : ℕ) :
    K < Skin.traj μ ρ K (fun _ => D) (n + 1) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    show K < μ * Skin.traj μ ρ K (fun _ => D) (n + 1) + ρ * D
    nlinarith [mul_le_mul_of_nonneg_left ih.le hμ]

/-- **Outside the window: a steady admissible disturbance drives survival to 0.** -/
theorem skin_out_of_window_dies {c μ ρ K D : ℝ} (hμ : 0 ≤ μ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (h : K < μ * K + ρ * D) (hc0 : 0 < c) (hc1 : c ≤ 1) {ε : ℝ} (hε : ε < 1) :
    |K| ≤ K ∧ (∀ n, |(fun _ => D : ℕ → ℝ) n| ≤ D) ∧
    ∃ n, surv (hzSkin c μ ρ K K (fun _ => D)) n < 1 - ε := by
  refine ⟨(abs_of_nonneg hK).le, fun _ => (abs_of_nonneg hD).le, ?_⟩
  have hconst : hzSkin c μ ρ K K (fun _ => D) = fun _ => c := by
    funext i
    unfold hzSkin
    simp [lt_of_lt_of_le (steady_push_above hμ h i) (le_abs_self _)]
  rw [hconst]
  exact const_hazard_dies hc0 hc1 hε

end FiveOrgans.SkinViability
