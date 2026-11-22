import FiveOrgans.BrakeDelay2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The delayed brake's edge gain `k_d = 2 sin(π / (2(2d+1)))` is marginal

Signal `x (n + d + 1) = x (n + d) - k * x n`. Let `θ_d = π/(2d+1)` and `k_d = 2 sin(θ_d/2)`.

* `edge_rec` — `x n = cos(n θ_d)` solves the recurrence at `k = k_d`, for every `d`.
  (Real form of: `e^{iθ_d}` is a root of `z^(d+1) - z^d + k_d` on the unit circle.)
  Proof: `cos A' - cos A = -2 sin((A+A')/2) sin(θ/2)` and `(d + 1/2) θ_d = π/2`.
* `edge_bounded`, `edge_no_decay` — that trajectory is bounded by 1 but returns to 1
  infinitely often: at `k_d` the brake neither diverges nor settles. The edge is marginal.
* `edge_pos`, `edge_le_one`, `edge_strict_anti` — `0 < k_d ≤ 1` for `d ≥ 1`, and `k_d`
  strictly decreases in `d`: longer delay, lower edge.
* `edge_one` — `k_1 = 1` (agrees with `BrakeDelay`: window `k ≤ 1`).
* `edge_two` — `k_2² + k_2 = 1` (agrees with `BrakeDelay2.delay2_window`: `k² + k < 1`).

`k_d` is the exact edge for every `d ≥ 1`: see `BrakeDelayExact` (below / above) and
`BrakeDelayAtEdge` (every trajectory bounded at `k_d` itself).
That needs the Jury / Schur–Cohn root-location argument. Proved so far: bounded for
`k ≤ d^d/(d+1)^(d+1)` (`BrakeDelayD`) and unbounded for `k > 1` (`BrakeDelayUnstable`).
-/

namespace FiveOrgans.BrakeDelayEdge
open Real

/-- The edge angle `θ_d = π / (2d + 1)`. -/
noncomputable def θ (d : ℕ) : ℝ := π / (2 * d + 1)

/-- The edge gain `k_d = 2 sin(θ_d / 2)`. -/
noncomputable def kEdge (d : ℕ) : ℝ := 2 * sin (θ d / 2)

theorem half_turn (d : ℕ) : ((d : ℝ) + 1 / 2) * θ d = π / 2 := by
  unfold θ
  have : (2 * (d : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- **At the edge gain, `cos(n θ_d)` solves the delayed brake.** -/
theorem edge_rec (d n : ℕ) :
    cos (((n + d + 1 : ℕ) : ℝ) * θ d)
      = cos (((n + d : ℕ) : ℝ) * θ d) - kEdge d * cos ((n : ℝ) * θ d) := by
  have h := Real.cos_sub_cos (((n : ℝ) + d + 1) * θ d) (((n : ℝ) + d) * θ d)
  have e1 : (((n : ℝ) + d + 1) * θ d + ((n : ℝ) + d) * θ d) / 2
      = (n : ℝ) * θ d + π / 2 := by
    have := half_turn d
    linear_combination this
  have e2 : (((n : ℝ) + d + 1) * θ d - ((n : ℝ) + d) * θ d) / 2 = θ d / 2 := by ring
  rw [e1, e2, Real.sin_add_pi_div_two] at h
  unfold kEdge
  push_cast
  linarith

theorem edge_bounded (d n : ℕ) : |cos ((n : ℝ) * θ d)| ≤ 1 := abs_cos_le_one _

/-- **No decay at the edge:** the trajectory returns to 1 beyond every horizon. -/
theorem edge_no_decay (d N : ℕ) : ∃ n, N ≤ n ∧ cos ((n : ℝ) * θ d) = 1 := by
  refine ⟨(2 * d + 1) * 2 * N, ?_, ?_⟩
  · nlinarith
  · have : (((2 * d + 1) * 2 * N : ℕ) : ℝ) * θ d = (N : ℝ) * (2 * π) := by
      unfold θ
      have : (2 * (d : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
    rw [this, Real.cos_nat_mul_two_pi]

theorem θ_pos (d : ℕ) : 0 < θ d := by unfold θ; positivity

theorem half_le (d : ℕ) (hd : 1 ≤ d) : θ d / 2 ≤ π / 6 := by
  unfold θ
  have h3 : (3 : ℝ) ≤ 2 * d + 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [pi_pos]

theorem edge_pos (d : ℕ) : 0 < kEdge d := by
  unfold kEdge
  have h0 := θ_pos d
  have : θ d / 2 < π := by
    unfold θ
    have : (1 : ℝ) ≤ 2 * d + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    rw [div_div, div_lt_iff₀ (by positivity)]
    nlinarith [pi_pos]
  have := sin_pos_of_pos_of_lt_pi (by linarith) this
  linarith

theorem edge_le_one (d : ℕ) (hd : 1 ≤ d) : kEdge d ≤ 1 := by
  unfold kEdge
  have h := sin_le_sin_of_le_of_le_pi_div_two (x := θ d / 2) (y := π / 6)
    (by linarith [θ_pos d, pi_pos]) (by linarith [pi_pos]) (half_le d hd)
  rw [sin_pi_div_six] at h
  linarith

/-- **Longer delay, lower edge.** -/
theorem edge_strict_anti (d : ℕ) : kEdge (d + 1) < kEdge d := by
  unfold kEdge
  have hlt : θ (d + 1) / 2 < θ d / 2 := by
    unfold θ
    push_cast
    have h1 : (0 : ℝ) < 2 * d + 1 := by positivity
    rw [div_div, div_div, div_lt_div_iff_of_pos_left pi_pos (by positivity) (by positivity)]
    nlinarith
  have hθ : θ d / 2 ≤ π / 2 := by
    unfold θ
    have : (1 : ℝ) ≤ 2 * d + 1 := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [pi_pos]
  have := sin_lt_sin_of_lt_of_le_pi_div_two
    (by linarith [θ_pos (d + 1), pi_pos]) hθ hlt
  linarith

/-- One-step delay: edge 1. -/
theorem edge_one : kEdge 1 = 1 := by
  unfold kEdge θ
  have : π / (2 * ((1 : ℕ) : ℝ) + 1) / 2 = π / 6 := by push_cast; ring
  rw [this, sin_pi_div_six]
  norm_num

/-- Two-step delay: the edge solves `k² + k = 1`, the boundary of `delay2_window`. -/
theorem edge_two : kEdge 2 ^ 2 + kEdge 2 = 1 := by
  have hθ : θ 2 / 2 = π / 10 := by unfold θ; push_cast; ring
  have hc : cos (π / 5) = 1 - 2 * sin (π / 10) ^ 2 := by
    have h := cos_two_mul (π / 10)
    have h2 := sin_sq_add_cos_sq (π / 10)
    rw [show 2 * (π / 10) = π / 5 by ring] at h
    linarith
  rw [cos_pi_div_five] at hc
  have hk : kEdge 2 = 2 * sin (π / 10) := by unfold kEdge; rw [hθ]
  have hpos := edge_pos 2
  set k := kEdge 2
  have hsq : k ^ 2 = (3 - √5) / 2 := by rw [hk]; nlinarith
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h51 : 1 < √5 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hfac : (k - (√5 - 1) / 2) * (k + (√5 - 1) / 2) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · have : k = (√5 - 1) / 2 := by linarith
    rw [hsq, this]; ring
  · nlinarith

end FiveOrgans.BrakeDelayEdge
