import FiveOrgans.Brake
import FiveOrgans.ViabilityStochastic

/-!
# Brake × Viability: a brake in its window is what makes long-run survival possible

First cross-organ theorem. The deviation follows the brake model
`x n = (g - b)^n x₀` (`Brake.traj`). Each step the agent fails with a hazard proportional to
the current deviation, capped at 1: `h n = min 1 (c |x n|)`.

* `brake_in_window_viable` — if `|g - b| < 1` then for every horizon
  `P(stay) ≥ 1 - c|x₀| / (1 - |g - b|)`. The hazard is summable because the brake shrinks the
  deviation geometrically.
* `brake_out_of_window_dies` — if `|g - b| ≥ 1`, `c > 0` and `x₀ ≠ 0`, then for every `ε < 1`
  survival eventually falls below `1 - ε`. The hazard never falls below `min 1 (c|x₀|) > 0`.

So the brake's stability window (`Brake.window_iff`, strict interior) is exactly where a
deviation-driven failure rate can be summable. This links "keep the error bounded" to "survive
in the long run".
-/

namespace FiveOrgans.BrakeViability
open Finset FiveOrgans.ViabilityStochastic

/-- Deviation-driven hazard, capped at 1. -/
noncomputable def hz (c g b x₀ : ℝ) (n : ℕ) : ℝ := min 1 (c * |Brake.traj g b x₀ n|)

theorem abs_traj (g b x₀ : ℝ) (n : ℕ) : |Brake.traj g b x₀ n| = |g - b| ^ n * |x₀| := by
  unfold Brake.traj; rw [abs_mul, abs_pow]

theorem hz_mem {c g b x₀ : ℝ} (hc : 0 ≤ c) (n : ℕ) : 0 ≤ hz c g b x₀ n ∧ hz c g b x₀ n ≤ 1 :=
  ⟨le_min zero_le_one (mul_nonneg hc (abs_nonneg _)), min_le_left _ _⟩

theorem geom_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) :
    ∑ i ∈ range n, r ^ i ≤ 1 / (1 - r) := by
  have hg := geom_sum_mul r n
  rw [le_div_iff₀ (by linarith)]
  have : 0 ≤ r ^ n := pow_nonneg h0 n
  nlinarith

/-- **In the window, the hazard is summable and survival stays above `1 - ε`.** -/
theorem brake_in_window_viable {c g b x₀ : ℝ} (hc : 0 ≤ c) (hw : |g - b| < 1) (n : ℕ) :
    1 - c * |x₀| / (1 - |g - b|) ≤ surv (hz c g b x₀) n := by
  apply budget_viable _ (hz_mem hc)
  intro m
  calc ∑ i ∈ range m, hz c g b x₀ i
      ≤ ∑ i ∈ range m, c * |x₀| * |g - b| ^ i := by
        apply sum_le_sum; intro i _
        refine (min_le_right _ _).trans (le_of_eq ?_)
        rw [abs_traj]; ring
    _ = c * |x₀| * ∑ i ∈ range m, |g - b| ^ i := by rw [mul_sum]
    _ ≤ c * |x₀| * (1 / (1 - |g - b|)) :=
        mul_le_mul_of_nonneg_left (geom_le (abs_nonneg _) hw m)
          (mul_nonneg hc (abs_nonneg _))
    _ = c * |x₀| / (1 - |g - b|) := by ring

/-- Survival under hazards at least `h₀` is at most `(1 - h₀)^n`. -/
theorem surv_le_pow (h : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) {h₀ : ℝ}
    (hlo : ∀ i, h₀ ≤ h i) (n : ℕ) : surv h n ≤ (1 - h₀) ^ n := by
  induction n with
  | zero => simp [surv]
  | succ n ih =>
    rw [surv_succ, pow_succ]
    have hs := (surv_mem h hh n).1
    have h2 : 0 ≤ 1 - h n := by linarith [(hh n).2]
    exact mul_le_mul ih (by linarith [hlo n]) h2 (hs.trans ih)

/-- **Out of the window, survival goes to 0.** -/
theorem brake_out_of_window_dies {c g b x₀ : ℝ} (hc : 0 < c) (hx : x₀ ≠ 0)
    (hw : 1 ≤ |g - b|) {ε : ℝ} (hε : ε < 1) :
    ∃ n, surv (hz c g b x₀) n < 1 - ε := by
  set h₀ := min 1 (c * |x₀|) with hh₀
  have hpos : 0 < h₀ := lt_min one_pos (mul_pos hc (abs_pos.mpr hx))
  have hlo : ∀ i, h₀ ≤ hz c g b x₀ i := by
    intro i
    unfold hz
    apply min_le_min_left
    rw [abs_traj]
    have : 1 ≤ |g - b| ^ i := one_le_pow₀ hw
    have : |x₀| ≤ |g - b| ^ i * |x₀| := le_mul_of_one_le_left (abs_nonneg _) this
    exact mul_le_mul_of_nonneg_left this hc.le
  obtain ⟨n, hn⟩ := const_hazard_dies hpos (min_le_left _ _) hε
  rw [surv_const] at hn
  exact ⟨n, lt_of_le_of_lt (surv_le_pow _ (hz_mem hc.le) hlo n) hn⟩

end FiveOrgans.BrakeViability
