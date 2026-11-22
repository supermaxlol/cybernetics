import FiveOrgans.Brake
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The delayed Brake: lag shrinks the stable window

No delay (`Brake.lean`, gain `g = 1`): `x (n+1) = x n - k * x n`, bounded iff `0 ≤ k ≤ 2`.

One-step delay: the Brake acts on the *previous* signal,

  `x (n+2) = x (n+1) - k * x n`.

Method: the energy `E n = x(n+1)^2 - x(n+1) x(n) + k x(n)^2` satisfies
`E (n+1) = k * E n` exactly (`E_succ`), so `E n = k^n * E 0`. For `k > 1/4` the
energy is positive definite.

Results.
* `delayed_bounded`   — `1/4 < k ≤ 1`: bounded for every start.
* `delayed_unbounded` — `k > 1`: unbounded for every nonzero start.
* `delay_shrinks_window` — every `k ∈ (1, 2]` is stable without delay and unstable
  with a one-step delay. The same Brake strength that works on fresh information
  blows up on stale information.

Not proved here: the region `k ≤ 1/4` (for the record, the delayed window is `0 ≤ k ≤ 1`),
and delays `d ≥ 2`. Both were later closed: `BrakeDelayD.delay1_window` (d = 1), and
`BrakeDelayExact.exact_window` (every d ≥ 1: edge `2 sin(π/(2(2d+1)))`).
-/

namespace FiveOrgans.BrakeDelay

/-- Signal with a one-step-delayed brake. -/
def dx (k x₀ x₁ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | 1 => x₁
  | n + 2 => dx k x₀ x₁ (n + 1) - k * dx k x₀ x₁ n

theorem dx_succ_succ (k x₀ x₁ : ℝ) (n : ℕ) :
    dx k x₀ x₁ (n + 2) = dx k x₀ x₁ (n + 1) - k * dx k x₀ x₁ n := rfl

/-- Quadratic energy. -/
def Q (k a b : ℝ) : ℝ := a ^ 2 - a * b + k * b ^ 2

def E (k x₀ x₁ : ℝ) (n : ℕ) : ℝ := Q k (dx k x₀ x₁ (n + 1)) (dx k x₀ x₁ n)

theorem E_succ (k x₀ x₁ : ℝ) (n : ℕ) : E k x₀ x₁ (n + 1) = k * E k x₀ x₁ n := by
  unfold E Q
  rw [show n + 1 + 1 = n + 2 from rfl, dx_succ_succ]
  ring

theorem E_formula (k x₀ x₁ : ℝ) (n : ℕ) : E k x₀ x₁ n = k ^ n * E k x₀ x₁ 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [E_succ, ih, pow_succ]; ring

theorem Q_lower {k : ℝ} (a b : ℝ) : (k - 1/4) * b ^ 2 ≤ Q k a b := by
  unfold Q; nlinarith [sq_nonneg (a - b / 2)]

theorem Q_pos {k a b : ℝ} (hk : 1/4 < k) (h : a ≠ 0 ∨ b ≠ 0) : 0 < Q k a b := by
  unfold Q
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := by tauto
    have : 0 < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha))
    nlinarith
  · have hb2 : 0 < b ^ 2 := lt_of_le_of_ne (sq_nonneg b) (Ne.symm (pow_ne_zero 2 hb))
    nlinarith [sq_nonneg (a - b / 2)]

theorem Q_upper {k : ℝ} (hk : 0 ≤ k) (a b : ℝ) : Q k a b ≤ (k + 3/2) * (a ^ 2 + b ^ 2) := by
  unfold Q
  nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b, mul_nonneg hk (sq_nonneg a)]

/-- Moderate delayed brake: bounded. -/
theorem delayed_bounded {k : ℝ} (h1 : 1/4 < k) (h2 : k ≤ 1) (x₀ x₁ : ℝ) :
    ∃ B, ∀ n, |dx k x₀ x₁ n| ≤ B := by
  have hc : 0 < k - 1/4 := by linarith
  have hE0 : 0 ≤ E k x₀ x₁ 0 :=
    le_trans (mul_nonneg hc.le (sq_nonneg _)) (Q_lower _ _)
  refine ⟨1 + E k x₀ x₁ 0 / (k - 1/4), fun n => ?_⟩
  have hpow : k ^ n ≤ 1 := pow_le_one₀ (by linarith) h2
  have hEn : E k x₀ x₁ n ≤ E k x₀ x₁ 0 := by
    rw [E_formula]; nlinarith [pow_nonneg (show (0:ℝ) ≤ k by linarith) n]
  have hlow : (k - 1/4) * (dx k x₀ x₁ n) ^ 2 ≤ E k x₀ x₁ n := Q_lower _ _
  have hsq : (dx k x₀ x₁ n) ^ 2 ≤ E k x₀ x₁ 0 / (k - 1/4) := by
    rw [le_div_iff₀ hc]; nlinarith
  have habs : |dx k x₀ x₁ n| ≤ 1 + (dx k x₀ x₁ n) ^ 2 := by
    nlinarith [sq_abs (dx k x₀ x₁ n), sq_nonneg (|dx k x₀ x₁ n| - 1)]
  linarith

/-- Strong delayed brake: unbounded from every nonzero start. -/
theorem delayed_unbounded {k x₀ x₁ : ℝ} (hk : 1 < k) (h : x₀ ≠ 0 ∨ x₁ ≠ 0) (B : ℝ) :
    ∃ n, B < |dx k x₀ x₁ n| := by
  by_contra hcon
  push Not at hcon
  have hE0 : 0 < E k x₀ x₁ 0 := Q_pos (by linarith) h.symm
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((k + 3/2) * (2 * B ^ 2) / E k x₀ x₁ 0) hk
  rw [div_lt_iff₀ hE0] at hn
  have hup : E k x₀ x₁ n ≤ (k + 3/2) * ((dx k x₀ x₁ (n + 1)) ^ 2 + (dx k x₀ x₁ n) ^ 2) :=
    Q_upper (by linarith) _ _
  have hsq : ∀ m, (dx k x₀ x₁ m) ^ 2 ≤ B ^ 2 := fun m => by
    have hm := hcon m
    nlinarith [abs_nonneg (dx k x₀ x₁ m), sq_abs (dx k x₀ x₁ m)]
  rw [E_formula] at hup
  nlinarith [hsq n, hsq (n + 1)]

/-- Delay shrinks the window: every `k ∈ (1, 2]` is stable on fresh information
(no-delay Brake with `g = 1`) and unstable on one-step-stale information. -/
theorem delay_shrinks_window {k : ℝ} (h1 : 1 < k) (h2 : k ≤ 2) :
    (∀ x₀ : ℝ, ∃ B, ∀ n, |Brake.traj 1 k x₀ n| ≤ B) ∧
    (∀ x₀ x₁ : ℝ, (x₀ ≠ 0 ∨ x₁ ≠ 0) → ∀ B, ∃ n, B < |dx k x₀ x₁ n|) := by
  refine ⟨fun x₀ => ⟨|x₀|, fun n => Brake.bounded_of_window ?_ x₀ n⟩,
    fun x₀ x₁ h B => delayed_unbounded h1 h B⟩
  rw [abs_le]; constructor <;> linarith

end FiveOrgans.BrakeDelay
