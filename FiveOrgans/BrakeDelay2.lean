import FiveOrgans.BrakeDelay
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.LinearCombination

/-!
# Two-step delay: the stable window shrinks again

Brake acting on information two steps old:

  `x (n+3) = x (n+2) - k * x n`,   started at `(0, 0, 1)`.

Method (reduce to the one-step energy trick). The characteristic polynomial
`z³ - z² + k` has a real root `ρ`. Factor it out: `y n = x (n+1) - ρ x n` obeys a
second-order recurrence (`y_rec`) with coefficients `a = ρ - 1`, `b = ρ² - ρ`, so the
energy `E n = y(n+1)² + a y(n+1) y(n) + b y(n)²` satisfies `E (n+1) = b · E n`
(`E_succ`), hence `E n = bⁿ` from this start (`E_formula`).

Results.
* `root_exists` — for `k > 0` with `k² + k > 1` there is a root `ρ ∈ (-k, 0)`, and then
  `b = -k/ρ > 1` (`b_gt_one`).
* `delay2_unbounded` — for every `k` with `k² + k > 1` (i.e. `k > (√5-1)/2 ≈ 0.618`)
  the two-step-delayed brake blows up.
* `delay2_shrinks_window` — every `k ∈ ((√5-1)/2, 1]` is bounded for **every** start
  with a one-step delay (`BrakeDelay.delayed_bounded`) and unbounded with a two-step
  delay. With `delay_shrinks_window`: no delay works up to `k = 2`, one step up to
  `k = 1`, two steps fails already above `≈ 0.618`.

* `delay2_bounded` — for `4/27 < k` with `k² + k < 1`, bounded from **every** start.
  So the two-step window's upper edge is exactly `(√5-1)/2` (= `2 sin(π/10)`).
* `delay2_bounded_small` — `0 < k ≤ 4/27` bounded too (positive-root deflation).
* `delay2_window` — for `k > 0`: bounded iff below `(√5-1)/2` (edge itself not covered). General `d` (window `2 sin(π/(2(2d+1)))`): closed in `BrakeDelayExact.exact_window`.
-/

namespace FiveOrgans.BrakeDelay2

/-- Signal with a two-step-delayed brake, started at (0, 0, 1). -/
def dx (k : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => dx k (n + 2) - k * dx k n

theorem dx_succ3 (k : ℝ) (n : ℕ) : dx k (n + 3) = dx k (n + 2) - k * dx k n := rfl

/-- Deflated signal. -/
def y (k ρ : ℝ) (n : ℕ) : ℝ := dx k (n + 1) - ρ * dx k n

theorem y_rec {k ρ : ℝ} (hk : ρ ^ 3 - ρ ^ 2 + k = 0) (n : ℕ) :
    y k ρ (n + 2) = -(ρ - 1) * y k ρ (n + 1) - (ρ ^ 2 - ρ) * y k ρ n := by
  unfold y
  rw [show n + 2 + 1 = n + 3 from rfl, dx_succ3, show n + 1 + 1 = n + 2 from rfl]
  linear_combination (-(dx k n)) * hk

def E (k ρ : ℝ) (n : ℕ) : ℝ :=
  y k ρ (n + 1) ^ 2 + (ρ - 1) * y k ρ (n + 1) * y k ρ n + (ρ ^ 2 - ρ) * y k ρ n ^ 2

theorem E_succ {k ρ : ℝ} (hk : ρ ^ 3 - ρ ^ 2 + k = 0) (n : ℕ) :
    E k ρ (n + 1) = (ρ ^ 2 - ρ) * E k ρ n := by
  unfold E
  rw [show n + 1 + 1 = n + 2 from rfl, y_rec hk]
  ring

theorem E_formula {k ρ : ℝ} (hk : ρ ^ 3 - ρ ^ 2 + k = 0) (n : ℕ) :
    E k ρ n = (ρ ^ 2 - ρ) ^ n := by
  induction n with
  | zero => simp [E, y, dx]
  | succ n ih => rw [E_succ hk, ih, pow_succ]; ring

theorem root_exists {k : ℝ} (hk0 : 0 < k) (hk : 1 < k ^ 2 + k) :
    ∃ ρ, -k < ρ ∧ ρ < 0 ∧ ρ ^ 3 - ρ ^ 2 + k = 0 := by
  let f : ℝ → ℝ := fun ρ => ρ ^ 3 - ρ ^ 2 + k
  have hcont : ContinuousOn f (Set.Icc (-k) 0) := (by fun_prop : Continuous f).continuousOn
  have hlo : f (-k) < 0 := by simp only [f]; nlinarith
  have hhi : 0 < f 0 := by simp only [f]; linarith
  obtain ⟨ρ, ⟨h1, h2⟩, hρ⟩ :=
    intermediate_value_Icc (by linarith) hcont ⟨hlo.le, hhi.le⟩
  refine ⟨ρ, lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_, hρ⟩
  · rintro rfl; exact absurd hρ hlo.ne
  · rintro rfl; exact absurd hρ hhi.ne'

theorem b_gt_one {k ρ : ℝ} (h1 : -k < ρ) (h2 : ρ < 0) (hk : ρ ^ 3 - ρ ^ 2 + k = 0) :
    1 < ρ ^ 2 - ρ := by
  have hk' : (ρ ^ 2 - ρ) * (-ρ) = k := by linear_combination -hk
  nlinarith

theorem E_upper {a b v w : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    v ^ 2 + a * v * w + b * w ^ 2 ≤ (1 + b - a) * (v ^ 2 + w ^ 2) := by
  nlinarith [mul_nonneg (neg_nonneg.2 ha) (sq_nonneg (v + w)),
    mul_nonneg hb (sq_nonneg v), mul_nonneg (neg_nonneg.2 ha) (sq_nonneg v),
    mul_nonneg (neg_nonneg.2 ha) (sq_nonneg w), sq_nonneg w]

/-- Two-step-delayed brake with `k² + k > 1` blows up. -/
theorem delay2_unbounded {k : ℝ} (hk0 : 0 < k) (hk : 1 < k ^ 2 + k) (B : ℝ) :
    ∃ n, B < |dx k n| := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ρ, h1, h2, hρ⟩ := root_exists hk0 hk
  have hb := b_gt_one h1 h2 hρ
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hcon 0)
  -- |y n| ≤ (1 - ρ) B
  have hy : ∀ n, y k ρ n ^ 2 ≤ ((1 - ρ) * B) ^ 2 := fun n => by
    have habs : |y k ρ n| ≤ (1 - ρ) * B := by
      unfold y
      calc |dx k (n + 1) - ρ * dx k n| ≤ |dx k (n + 1)| + |ρ * dx k n| := abs_sub _ _
        _ = |dx k (n + 1)| + (-ρ) * |dx k n| := by rw [abs_mul, abs_of_neg h2]
        _ ≤ B + (-ρ) * B := by
          gcongr
          · exact hcon _
          · linarith
          · exact hcon _
        _ = (1 - ρ) * B := by ring
    have h0 : 0 ≤ (1 - ρ) * B := by nlinarith
    nlinarith [abs_nonneg (y k ρ n), sq_abs (y k ρ n)]
  set Cst := (1 + (ρ ^ 2 - ρ) - (ρ - 1)) * (2 * ((1 - ρ) * B) ^ 2)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt Cst hb
  have hup : E k ρ n ≤ (1 + (ρ ^ 2 - ρ) - (ρ - 1)) * (y k ρ (n + 1) ^ 2 + y k ρ n ^ 2) :=
    E_upper (by linarith) (by linarith)
  rw [E_formula hρ] at hup
  have hc : 0 ≤ 1 + (ρ ^ 2 - ρ) - (ρ - 1) := by linarith
  nlinarith [hy n, hy (n + 1), mul_le_mul_of_nonneg_left
    (add_le_add (hy (n + 1)) (hy n)) hc]

/-- The second step of delay shrinks the window again: on `((√5-1)/2, 1]` a one-step
delay is bounded from every start, a two-step delay is not. -/
theorem delay2_shrinks_window {k : ℝ} (hk : 1 < k ^ 2 + k) (h1 : k ≤ 1) (hk0 : 0 < k) :
    (∀ x₀ x₁ : ℝ, ∃ B, ∀ n, |BrakeDelay.dx k x₀ x₁ n| ≤ B) ∧
    (∀ B, ∃ n, B < |dx k n|) :=
  ⟨fun x₀ x₁ => BrakeDelay.delayed_bounded (by nlinarith) h1 x₀ x₁,
    fun B => delay2_unbounded hk0 hk B⟩

/-- Non-vacuity: `k = 1`. -/
theorem delay2_instance :
    (∀ x₀ x₁ : ℝ, ∃ B, ∀ n, |BrakeDelay.dx 1 x₀ x₁ n| ≤ B) ∧
    (∀ B, ∃ n, B < |dx 1 n|) :=
  delay2_shrinks_window (by norm_num) le_rfl one_pos

/-! ## The bounded side, for every start

Any sequence with `x (n+3) = x (n+2) - k x n`. For `4/27 < k` and `k² + k < 1` the
real root lies in `(-1, -k)`, so `b = -k/ρ < 1`, the energy is positive definite
(`ρ < -1/3`), and the signal stays bounded. -/

section General
variable {k ρ : ℝ} {x : ℕ → ℝ}

def yg (ρ : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ := x (n + 1) - ρ * x n

def Eg (ρ : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  yg ρ x (n + 1) ^ 2 + (ρ - 1) * yg ρ x (n + 1) * yg ρ x n + (ρ ^ 2 - ρ) * yg ρ x n ^ 2

theorem Eg_succ (hrec : ∀ n, x (n + 3) = x (n + 2) - k * x n)
    (hk : ρ ^ 3 - ρ ^ 2 + k = 0) (n : ℕ) : Eg ρ x (n + 1) = (ρ ^ 2 - ρ) * Eg ρ x n := by
  have hy : yg ρ x (n + 2) = -(ρ - 1) * yg ρ x (n + 1) - (ρ ^ 2 - ρ) * yg ρ x n := by
    unfold yg
    rw [show n + 2 + 1 = n + 3 from rfl, hrec, show n + 1 + 1 = n + 2 from rfl]
    linear_combination (-(x n)) * hk
  unfold Eg
  rw [show n + 1 + 1 = n + 2 from rfl, hy]
  ring

theorem Eg_formula (hrec : ∀ n, x (n + 3) = x (n + 2) - k * x n)
    (hk : ρ ^ 3 - ρ ^ 2 + k = 0) (n : ℕ) : Eg ρ x n = (ρ ^ 2 - ρ) ^ n * Eg ρ x 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Eg_succ hrec hk, ih, pow_succ]; ring

end General

theorem root_stable {k : ℝ} (hk1 : 4 / 27 < k) (hk : k ^ 2 + k < 1) :
    ∃ ρ, -1 < ρ ∧ ρ < -k ∧ ρ < -1 / 3 ∧ ρ ^ 3 - ρ ^ 2 + k = 0 := by
  let f : ℝ → ℝ := fun ρ => ρ ^ 3 - ρ ^ 2 + k
  have hk0 : 0 < k := by linarith
  have hcont : ContinuousOn f (Set.Icc (-1) (-k)) := (by fun_prop : Continuous f).continuousOn
  have hlo : f (-1) < 0 := by simp only [f]; nlinarith
  have hhi : 0 < f (-k) := by simp only [f]; nlinarith
  obtain ⟨ρ, ⟨h1, h2⟩, hρ⟩ :=
    intermediate_value_Icc (by nlinarith) hcont ⟨hlo.le, hhi.le⟩
  simp only [f] at hρ
  have h1' : -1 < ρ := lt_of_le_of_ne h1 (by rintro rfl; norm_num at hρ; linarith)
  have h2' : ρ < -k := lt_of_le_of_ne h2 (by rintro rfl; simp only [f] at hhi; linarith)
  refine ⟨ρ, h1', h2', ?_, hρ⟩
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg (sq_nonneg ρ) (show (0:ℝ) ≤ ρ + 1 / 3 by linarith),
    mul_nonneg (sq_nonneg (ρ + 1 / 3)) (show (0:ℝ) ≤ -ρ by linarith)]

/-- Two-step-delayed brake with `4/27 < k`, `k² + k < 1`: bounded from every start. -/
theorem delay2_bounded {k : ℝ} (hk1 : 4 / 27 < k) (hk : k ^ 2 + k < 1) {x : ℕ → ℝ}
    (hrec : ∀ n, x (n + 3) = x (n + 2) - k * x n) : ∃ B, ∀ n, |x n| ≤ B := by
  obtain ⟨ρ, h1, h2, h3, hρ⟩ := root_stable hk1 hk
  have hk0 : 0 < k := by linarith
  set b := ρ ^ 2 - ρ with hbdef
  have hbk : b * (-ρ) = k := by rw [hbdef]; linear_combination -hρ
  have hb0 : 0 < b := by nlinarith
  have hb1 : b ≤ 1 := by nlinarith
  -- positive definiteness: Eg ≥ c · y²
  set c := b - (ρ - 1) ^ 2 / 4 with hc
  have hcpos : 0 < c := by rw [hc, hbdef]; nlinarith
  have hlow : ∀ n, c * yg ρ x n ^ 2 ≤ Eg ρ x n := fun n => by
    unfold Eg; rw [hc]
    nlinarith [sq_nonneg (yg ρ x (n + 1) + (ρ - 1) / 2 * yg ρ x n)]
  have hE0 : 0 ≤ Eg ρ x 0 := le_trans (mul_nonneg hcpos.le (sq_nonneg _)) (hlow 0)
  set Y := 1 + Eg ρ x 0 / c
  have hy : ∀ n, |yg ρ x n| ≤ Y := fun n => by
    have hEn : Eg ρ x n ≤ Eg ρ x 0 := by
      rw [Eg_formula hrec hρ]
      nlinarith [pow_le_one₀ hb0.le hb1 (n := n), pow_nonneg hb0.le n]
    have hsq : yg ρ x n ^ 2 ≤ Eg ρ x 0 / c := by
      rw [le_div_iff₀ hcpos]; nlinarith [hlow n]
    nlinarith [sq_abs (yg ρ x n), sq_nonneg (|yg ρ x n| - 1)]
  have hY : 0 ≤ Y := le_trans (abs_nonneg _) (hy 0)
  refine ⟨|x 0| + Y / (1 + ρ), fun n => ?_⟩
  have hr : 0 < 1 + ρ := by linarith
  induction n with
  | zero => have := div_nonneg hY hr.le; linarith
  | succ n ih =>
    have hx : x (n + 1) = ρ * x n + yg ρ x n := by unfold yg; ring
    rw [hx]
    calc |ρ * x n + yg ρ x n| ≤ |ρ * x n| + |yg ρ x n| := abs_add_le _ _
      _ = (-ρ) * |x n| + |yg ρ x n| := by rw [abs_mul, abs_of_neg (by linarith)]
      _ ≤ (-ρ) * (|x 0| + Y / (1 + ρ)) + Y := by
          gcongr
          · linarith
          · exact hy n
      _ ≤ |x 0| + Y / (1 + ρ) := by
          have hYr : Y = (1 + ρ) * (Y / (1 + ρ)) := by field_simp
          nlinarith [abs_nonneg (x 0), div_nonneg hY hr.le]

/-! ## The small-`k` side: positive-root deflation

For `0 < k ≤ 4/27` the cubic has a root `σ ∈ (0, 2/3]`. Then
`y (n+2) = (1-σ) y (n+1) + (σ-σ²) y n` has positive coefficients summing to `1 - σ² < 1`,
so `|y|` never exceeds its starting size, and `x (n+1) = σ x n + y n` with `σ < 1`
stays bounded. -/

theorem yg_rec {k ρ : ℝ} {x : ℕ → ℝ} (hrec : ∀ n, x (n + 3) = x (n + 2) - k * x n)
    (hk : ρ ^ 3 - ρ ^ 2 + k = 0) (n : ℕ) :
    yg ρ x (n + 2) = (1 - ρ) * yg ρ x (n + 1) + (ρ - ρ ^ 2) * yg ρ x n := by
  unfold yg
  rw [show n + 2 + 1 = n + 3 from rfl, hrec, show n + 1 + 1 = n + 2 from rfl]
  linear_combination (-(x n)) * hk

theorem root_small {k : ℝ} (hk0 : 0 < k) (hk : k ≤ 4 / 27) :
    ∃ σ, 0 < σ ∧ σ ≤ 2 / 3 ∧ σ ^ 3 - σ ^ 2 + k = 0 := by
  let f : ℝ → ℝ := fun σ => σ ^ 3 - σ ^ 2 + k
  have hcont : ContinuousOn f (Set.Icc 0 (2 / 3)) := (by fun_prop : Continuous f).continuousOn
  have hlo : f (2 / 3) ≤ 0 := by simp only [f]; norm_num; linarith
  have hhi : 0 < f 0 := by simp only [f]; norm_num; linarith
  obtain ⟨σ, ⟨h1, h2⟩, hσ⟩ :=
    intermediate_value_Icc' (by norm_num) hcont ⟨hlo, hhi.le⟩
  refine ⟨σ, lt_of_le_of_ne h1 ?_, h2, hσ⟩
  rintro rfl; exact absurd hσ hhi.ne'

/-- Two-step-delayed brake with `0 < k ≤ 4/27`: bounded from every start. -/
theorem delay2_bounded_small {k : ℝ} (hk0 : 0 < k) (hk : k ≤ 4 / 27) {x : ℕ → ℝ}
    (hrec : ∀ n, x (n + 3) = x (n + 2) - k * x n) : ∃ B, ∀ n, |x n| ≤ B := by
  obtain ⟨σ, h1, h2, hσ⟩ := root_small hk0 hk
  set Y := max |yg σ x 0| |yg σ x 1|
  have hc1 : 0 ≤ 1 - σ := by linarith
  have hc2 : 0 ≤ σ - σ ^ 2 := by nlinarith
  have hpair : ∀ n, |yg σ x n| ≤ Y ∧ |yg σ x (n + 1)| ≤ Y := by
    intro n
    induction n with
    | zero => exact ⟨le_max_left _ _, le_max_right _ _⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [show n + 1 + 1 = n + 2 from rfl, yg_rec hrec hσ]
      calc |(1 - σ) * yg σ x (n + 1) + (σ - σ ^ 2) * yg σ x n|
          ≤ |(1 - σ) * yg σ x (n + 1)| + |(σ - σ ^ 2) * yg σ x n| := abs_add_le _ _
        _ = (1 - σ) * |yg σ x (n + 1)| + (σ - σ ^ 2) * |yg σ x n| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hc1, abs_of_nonneg hc2]
        _ ≤ (1 - σ) * Y + (σ - σ ^ 2) * Y := by
          gcongr
          · exact ih.2
          · exact ih.1
        _ ≤ Y := by
          have hY : 0 ≤ Y := le_trans (abs_nonneg _) (le_max_left _ _)
          nlinarith [mul_nonneg (sq_nonneg σ) hY]
  have hY : 0 ≤ Y := le_trans (abs_nonneg _) (le_max_left _ _)
  have hr : 0 < 1 - σ := by linarith
  refine ⟨|x 0| + Y / (1 - σ), fun n => ?_⟩
  induction n with
  | zero => have := div_nonneg hY hr.le; linarith
  | succ n ih =>
    have hx : x (n + 1) = σ * x n + yg σ x n := by unfold yg; ring
    rw [hx]
    calc |σ * x n + yg σ x n| ≤ |σ * x n| + |yg σ x n| := abs_add_le _ _
      _ = σ * |x n| + |yg σ x n| := by rw [abs_mul, abs_of_pos h1]
      _ ≤ σ * (|x 0| + Y / (1 - σ)) + Y := by
          gcongr
          exact (hpair n).1
      _ ≤ |x 0| + Y / (1 - σ) := by
          have hYr : Y = (1 - σ) * (Y / (1 - σ)) := by field_simp
          nlinarith [abs_nonneg (x 0), div_nonneg hY hr.le]

/-- **The two-step window.** For `0 < k`: if `k² + k < 1` every trajectory is bounded;
if `k² + k > 1` the trajectory from `(0,0,1)` is unbounded. Edge: `k = (√5-1)/2`. -/
theorem delay2_window {k : ℝ} (hk0 : 0 < k) :
    (k ^ 2 + k < 1 → ∀ x : ℕ → ℝ, (∀ n, x (n + 3) = x (n + 2) - k * x n) →
        ∃ B, ∀ n, |x n| ≤ B) ∧
    (1 < k ^ 2 + k → ∀ B, ∃ n, B < |dx k n|) := by
  refine ⟨fun hk x hrec => ?_, fun hk B => delay2_unbounded hk0 hk B⟩
  rcases le_or_gt k (4 / 27) with h | h
  · exact delay2_bounded_small hk0 h hrec
  · exact delay2_bounded h hk hrec

end FiveOrgans.BrakeDelay2
