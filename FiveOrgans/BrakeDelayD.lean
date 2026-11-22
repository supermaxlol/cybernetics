import FiveOrgans.BrakeDelay
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.LinearCombination

/-!
# Brake with a general delay `d`: the small-gain side

Signal `x (n + d + 1) = x (n + d) - k * x n` (the brake acts on a reading `d` steps old).
Characteristic polynomial `z^(d+1) - z^d + k`.

Results (any `d ≥ 1`).
* `root_d` — for `0 < k ≤ (d/(d+1))^d / (d+1)` (= `d^d / (d+1)^(d+1)`, the maximum of
  `σ^d (1-σ)`) there is a root `σ ∈ (0,1)` with `σ^d (1-σ) = k`.
* `delayD_bounded_small` — in that range every trajectory is bounded, from every start.
  Proof: deflate by `σ`: `y n = x (n+1) - σ x n` satisfies
  `y (n+d) = (1-σ) (x (n+d) - σ^d x n)`, and `|x (n+m) - σ^m x n| (1-σ) ≤ Y (1-σ^m)`
  whenever the `y`'s in between are `≤ Y`; so `|y|` never exceeds the sum of its first `d`
  values, and `x` (contracted by `σ < 1`) stays bounded.
* `delay1_bounded_small` — `d = 1`, `0 < k ≤ 1/4`.

The guaranteed-bounded range shrinks with `d` (`d^d/(d+1)^(d+1) ≈ 1/(e(d+1))`). This is a
*sufficient* range only: the exact edge for general `d` (known to be `2 sin(π/(2(2d+1)))`)
is not proved here.
-/

namespace FiveOrgans.BrakeDelayD

/-- Deflated sequence. -/
def yd (σ : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ := x (n + 1) - σ * x n

theorem root_d {d : ℕ} (hd : 1 ≤ d) {k : ℝ} (hk0 : 0 < k)
    (hk : k ≤ ((d : ℝ) / (d + 1)) ^ d / (d + 1)) :
    ∃ σ, 0 < σ ∧ σ < 1 ∧ σ ^ d * (1 - σ) = k := by
  let g : ℝ → ℝ := fun σ => σ ^ d * (1 - σ)
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  have hb : (d : ℝ) / (d + 1) < 1 := by rw [div_lt_one hd1]; linarith
  have hb0 : (0 : ℝ) ≤ d / (d + 1) := by positivity
  have hcont : ContinuousOn g (Set.Icc 0 ((d : ℝ) / (d + 1))) :=
    (by fun_prop : Continuous g).continuousOn
  have hg0 : g 0 = 0 := by simp [g, zero_pow (by omega : d ≠ 0)]
  have hgb : g ((d : ℝ) / (d + 1)) = ((d : ℝ) / (d + 1)) ^ d / (d + 1) := by
    simp only [g]; field_simp; ring
  have hmem : k ∈ Set.Icc (g 0) (g ((d : ℝ) / (d + 1))) :=
    ⟨by rw [hg0]; exact hk0.le, by rw [hgb]; exact hk⟩
  obtain ⟨σ, ⟨h1, h2⟩, hσ⟩ := intermediate_value_Icc hb0 hcont hmem
  refine ⟨σ, lt_of_le_of_ne h1 ?_, lt_of_le_of_lt h2 hb, hσ⟩
  intro h
  have h' : g σ = 0 := h ▸ hg0
  linarith [hσ.symm.trans h']

/-- One-step telescoping bound. -/
theorem tele_bound {σ Y : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {x : ℕ → ℝ} (n : ℕ) :
    ∀ m, (∀ j < m, |yd σ x (n + j)| ≤ Y) →
      |x (n + m) - σ ^ m * x n| * (1 - σ) ≤ Y * (1 - σ ^ m) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hy
    have ihm := ih (fun j hj => hy j (by omega))
    have hym := hy m (by omega)
    have hT : x (n + (m + 1)) - σ ^ (m + 1) * x n
        = σ * (x (n + m) - σ ^ m * x n) + yd σ x (n + m) := by
      unfold yd; rw [show n + (m + 1) = n + m + 1 by omega]; ring
    rw [hT]
    have hc : 0 ≤ 1 - σ := by linarith
    calc |σ * (x (n + m) - σ ^ m * x n) + yd σ x (n + m)| * (1 - σ)
        ≤ (σ * |x (n + m) - σ ^ m * x n| + |yd σ x (n + m)|) * (1 - σ) := by
          gcongr
          calc _ ≤ |σ * (x (n + m) - σ ^ m * x n)| + |yd σ x (n + m)| := abs_add_le _ _
            _ = _ := by rw [abs_mul, abs_of_pos h0]
      _ = σ * (|x (n + m) - σ ^ m * x n| * (1 - σ)) + |yd σ x (n + m)| * (1 - σ) := by ring
      _ ≤ σ * (Y * (1 - σ ^ m)) + Y * (1 - σ) := by
          gcongr
      _ = Y * (1 - σ ^ (m + 1)) := by ring

theorem yd_shift {d : ℕ} {k σ : ℝ} {x : ℕ → ℝ}
    (hrec : ∀ n, x (n + d + 1) = x (n + d) - k * x n) (hσ : σ ^ d * (1 - σ) = k)
    (n : ℕ) : yd σ x (n + d) = (1 - σ) * (x (n + d) - σ ^ d * x n) := by
  unfold yd; rw [hrec]; linear_combination (x n) * hσ

/-- **General delay, small gain: bounded from every start.** -/
theorem delayD_bounded_small {d : ℕ} (hd : 1 ≤ d) {k : ℝ} (hk0 : 0 < k)
    (hk : k ≤ ((d : ℝ) / (d + 1)) ^ d / (d + 1)) {x : ℕ → ℝ}
    (hrec : ∀ n, x (n + d + 1) = x (n + d) - k * x n) : ∃ B, ∀ n, |x n| ≤ B := by
  obtain ⟨σ, h0, h1, hσ⟩ := root_d hd hk0 hk
  set Y := ∑ j ∈ Finset.range d, |yd σ x j| with hYdef
  have hY : 0 ≤ Y := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hall : ∀ n, |yd σ x n| ≤ Y := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases lt_or_ge n d with hn | hn
      · exact Finset.single_le_sum (f := fun j => |yd σ x j|)
          (fun j _ => abs_nonneg _) (Finset.mem_range.mpr hn)
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + d := ⟨n - d, by omega⟩
        have hb := tele_bound (Y := Y) h0 h1 m d
          (fun j hj => ih (m + j) (by omega))
        rw [yd_shift hrec hσ, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - σ)]
        have hp : 0 ≤ σ ^ d := pow_nonneg h0.le d
        nlinarith [abs_nonneg (x (m + d) - σ ^ d * x m)]
  have hr : 0 < 1 - σ := by linarith
  refine ⟨|x 0| + Y / (1 - σ), fun n => ?_⟩
  induction n with
  | zero => have := div_nonneg hY hr.le; linarith
  | succ n ih =>
    have hx : x (n + 1) = σ * x n + yd σ x n := by unfold yd; ring
    rw [hx]
    calc |σ * x n + yd σ x n| ≤ |σ * x n| + |yd σ x n| := abs_add_le _ _
      _ = σ * |x n| + |yd σ x n| := by rw [abs_mul, abs_of_pos h0]
      _ ≤ σ * (|x 0| + Y / (1 - σ)) + Y := by
          gcongr
          exact hall n
      _ ≤ |x 0| + Y / (1 - σ) := by
          have hYr : Y = (1 - σ) * (Y / (1 - σ)) := by field_simp
          nlinarith [abs_nonneg (x 0), div_nonneg hY hr.le]

/-- One-step delay (`x (n+2) = x (n+1) - k x n`), `0 < k ≤ 1/4`: bounded from every start. -/
theorem delay1_bounded_small {k : ℝ} (hk0 : 0 < k) (hk : k ≤ 1 / 4) {x : ℕ → ℝ}
    (hrec : ∀ n, x (n + 2) = x (n + 1) - k * x n) : ∃ B, ∀ n, |x n| ≤ B :=
  delayD_bounded_small (d := 1) le_rfl hk0 (by norm_num; linarith) hrec

end FiveOrgans.BrakeDelayD
