import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Brake: too little and too much both fail

Model. A signal amplifies itself with gain `g` each step; the Brake subtracts
`b` times the current signal:

  `x (n+1) = (g - b) * x n`,  so  `x n = (g - b)^n * x 0`.

Results.
* `bounded_of_window`   — if `|g - b| ≤ 1` the signal never exceeds its start.
* `unbounded_of_outside`— if `|g - b| > 1` and `x 0 ≠ 0` it grows without bound.
* `window_iff`          — the signal stays bounded iff `g - 1 ≤ b ≤ g + 1`.
  Under-braking (`b < g - 1`) runs away; over-braking (`b > g + 1`) overshoots
  into growing oscillation. The Brake is non-monotonic: there is a window.

Empirical link: navigator `no_brake` won most but ran energy pinned at 1.00
(H5: non-monotonic braking). This model has no delay; delayed feedback
(where stability shrinks as delay grows) is an open target (ASSUMPTIONS.md, B2).
-/

namespace FiveOrgans.Brake

/-- Signal after `n` steps with net gain `g - b`. -/
def traj (g b x₀ : ℝ) (n : ℕ) : ℝ := (g - b) ^ n * x₀

theorem traj_succ (g b x₀ : ℝ) (n : ℕ) :
    traj g b x₀ (n + 1) = (g - b) * traj g b x₀ n := by
  unfold traj; ring

theorem bounded_of_window {g b : ℝ} (h : |g - b| ≤ 1) (x₀ : ℝ) (n : ℕ) :
    |traj g b x₀ n| ≤ |x₀| := by
  unfold traj
  rw [abs_mul, abs_pow]
  have : |g - b| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) h
  have hx := abs_nonneg x₀
  nlinarith

theorem unbounded_of_outside {g b x₀ : ℝ} (h : 1 < |g - b|) (hx : x₀ ≠ 0) (B : ℝ) :
    ∃ n, B < |traj g b x₀ n| := by
  have hx' : 0 < |x₀| := abs_pos.mpr hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B / |x₀|) h
  refine ⟨n, ?_⟩
  unfold traj
  rw [abs_mul, abs_pow]
  rwa [div_lt_iff₀ hx'] at hn

/-- Bounded for every start iff the brake sits in the window `[g-1, g+1]`. -/
theorem window_iff {g b x₀ : ℝ} (hx : x₀ ≠ 0) :
    (∃ B, ∀ n, |traj g b x₀ n| ≤ B) ↔ (g - 1 ≤ b ∧ b ≤ g + 1) := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra hout
    have h1 : 1 < |g - b| := by
      rw [lt_abs]
      by_cases hb : g - 1 ≤ b
      · right; have : ¬ b ≤ g + 1 := fun h => hout ⟨hb, h⟩
        linarith
      · left; linarith
    obtain ⟨n, hn⟩ := unbounded_of_outside h1 hx B
    linarith [hB n]
  · rintro ⟨h1, h2⟩
    refine ⟨|x₀|, fun n => bounded_of_window ?_ x₀ n⟩
    rw [abs_le]; constructor <;> linarith

end FiveOrgans.Brake
