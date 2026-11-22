import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith

/-!
# The Skin: permeable enough to feed, tight enough to protect

Internal deviation `s` from the set point; viable iff `|s| ≤ K`. Each step the interior
retains a fraction `μ ∈ [0,1)` of its deviation (internal repair), and the boundary lets
through a fraction `ρ ≥ 0` (permeability) of an outside disturbance `d n` with `|d n| ≤ D`:

  `s (n+1) = μ * s n + ρ * d n`.

The organism must also take in enough: permeability at least `ρmin` (metabolic need).

Results.
* `skin_invariant` — if `μK + ρD ≤ K`, then **every** disturbance sequence keeps a viable
  start viable forever (robust, controlled invariance).
* `skin_breach` — if `μK + ρD > K`, some admissible disturbance breaks viability in one step.
* `skin_window` — a skin that both feeds and protects exists iff `ρmin · D ≤ (1-μ) K`.
  A closed skin (`ρ = 0`) is safe but starves; an open one is fed but breached.

Toy model: scalar, linear, worst-case disturbance. Selective (signal-dependent) filtering:
`SkinSelective`; stochastic disturbances: `SkinStochastic`.
-/

namespace FiveOrgans.Skin

def traj (μ ρ s₀ : ℝ) (d : ℕ → ℝ) : ℕ → ℝ
  | 0 => s₀
  | n + 1 => μ * traj μ ρ s₀ d n + ρ * d n

theorem skin_invariant {μ ρ K D s₀ : ℝ} {d : ℕ → ℝ} (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ)
    (h : μ * K + ρ * D ≤ K) (hd : ∀ n, |d n| ≤ D) (hs : |s₀| ≤ K) :
    ∀ n, |traj μ ρ s₀ d n| ≤ K := by
  intro n
  induction n with
  | zero => exact hs
  | succ n ih =>
    show |μ * traj μ ρ s₀ d n + ρ * d n| ≤ K
    calc |μ * traj μ ρ s₀ d n + ρ * d n|
        ≤ |μ * traj μ ρ s₀ d n| + |ρ * d n| := abs_add_le _ _
      _ = μ * |traj μ ρ s₀ d n| + ρ * |d n| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hμ, abs_of_nonneg hρ]
      _ ≤ μ * K + ρ * D := by
          nlinarith [mul_le_mul_of_nonneg_left ih hμ, mul_le_mul_of_nonneg_left (hd n) hρ]
      _ ≤ K := h

theorem skin_breach {μ ρ K D : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D) (h : K < μ * K + ρ * D) :
    ∃ (s₀ : ℝ) (d : ℕ → ℝ), |s₀| ≤ K ∧ (∀ n, |d n| ≤ D) ∧ K < |traj μ ρ s₀ d 1| := by
  refine ⟨K, fun _ => D, by rw [abs_of_nonneg hK], fun _ => by rw [abs_of_nonneg hD], ?_⟩
  exact lt_of_lt_of_le h (le_abs_self _)

/-- A boundary that both feeds (`ρ ≥ ρmin`) and protects exists iff `ρmin D ≤ (1-μ) K`. -/
theorem skin_window {μ K D ρmin : ℝ} (hD : 0 < D) :
    (∃ ρ, ρmin ≤ ρ ∧ μ * K + ρ * D ≤ K) ↔ ρmin * D ≤ (1 - μ) * K := by
  constructor
  · rintro ⟨ρ, h1, h2⟩
    nlinarith [mul_le_mul_of_nonneg_right h1 hD.le]
  · intro h
    exact ⟨ρmin, le_rfl, by linarith⟩

end FiveOrgans.Skin
