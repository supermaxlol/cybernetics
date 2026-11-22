import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Two speeds of memory

A memory trace updated at rate `η` (exponential moving average):

  `m (n+1) = (1 - η) * m n + η * y n`.

Two demands pull `η` in opposite directions.
* **Track change.** After a step change of size `Δ` the remaining error is
  `(1-η)^n · Δ` (`step_error`) — needs large `η`.
* **Ignore noise.** Under alternating noise `±σ` the trace settles into a ripple of
  amplitude `ησ / (2-η)` (`alt_orbit`, `alt_amplitude`, any start converges to it by
  `ema_diff`) — needs small `η`. Ripple ≤ δ iff `η ≤ 2δ/(σ+δ)` (`ripple_le_iff`).

Results.
* `single_rate_conflict` — if even the largest noise-safe rate is too slow to catch a
  change within `N` steps, **no single rate** satisfies both demands.
* `two_rates_suffice` — a fast trace (`η = 1`) and a slow trace (`η = 2δ/(σ+δ)`) each
  meet their own demand.
* `conflict_instance` — the hypothesis is not vacuous: with σ = 1, δ = 1/100, N = 10,
  ε = 1/2, no rate in `[0,1]` works.

Scope: deterministic worst-case signals, one scalar per demand. What this shows is that
a single learning rate cannot serve both "catch changes fast" and "stay steady under
noise"; it does not show brains or LLMs are built this way (EMP?). Stochastic noise
(variance `ησ²/(2-η)`) is the standard analogue and is not formalised here.
-/

namespace FiveOrgans.TwoSpeed

def ema (η m₀ : ℝ) (y : ℕ → ℝ) : ℕ → ℝ
  | 0 => m₀
  | n + 1 => (1 - η) * ema η m₀ y n + η * y n

theorem ema_succ (η m₀ : ℝ) (y : ℕ → ℝ) (n : ℕ) :
    ema η m₀ y (n + 1) = (1 - η) * ema η m₀ y n + η * y n := rfl

/-- Two traces with the same input forget their difference at rate `1 - η`. -/
theorem ema_diff (η a b : ℝ) (y : ℕ → ℝ) (n : ℕ) :
    ema η a y n - ema η b y n = (1 - η) ^ n * (a - b) := by
  induction n with
  | zero => simp [ema]
  | succ n ih => rw [ema_succ, ema_succ, pow_succ]; linear_combination (1 - η) * ih

/-- Lag after a step change. -/
theorem step_error (η Δ : ℝ) (n : ℕ) :
    Δ - ema η 0 (fun _ => Δ) n = (1 - η) ^ n * Δ := by
  induction n with
  | zero => simp [ema]
  | succ n ih => rw [ema_succ, pow_succ]; linear_combination (1 - η) * ih

/-- Periodic orbit under alternating noise. -/
theorem alt_orbit (η σ : ℝ) (hη : η ≠ 2) (n : ℕ) :
    ema η (-(η * σ / (2 - η))) (fun k => (-1) ^ k * σ) n
      = (-1) ^ n * (-(η * σ / (2 - η))) := by
  have h2 : (2 - η) ≠ 0 := sub_ne_zero.mpr (Ne.symm hη)
  induction n with
  | zero => simp [ema]
  | succ n ih =>
    rw [ema_succ, ih, pow_succ]
    field_simp
    ring

theorem alt_amplitude {η σ : ℝ} (h0 : 0 ≤ η) (h1 : η < 2) (hσ : 0 ≤ σ) (n : ℕ) :
    |ema η (-(η * σ / (2 - η))) (fun k => (-1) ^ k * σ) n| = η * σ / (2 - η) := by
  rw [alt_orbit η σ (by linarith) n, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_neg, abs_of_nonneg (div_nonneg (mul_nonneg h0 hσ) (by linarith))]

theorem ripple_le_iff {η σ δ : ℝ} (hσ : 0 ≤ σ) (hδ : 0 < δ) (h1 : η < 2) :
    η * σ / (2 - η) ≤ δ ↔ η ≤ 2 * δ / (σ + δ) := by
  rw [div_le_iff₀ (by linarith), le_div_iff₀ (by linarith)]
  constructor <;> intro h <;> nlinarith

theorem single_rate_conflict {σ δ ε : ℝ} {N : ℕ} (hσ : 0 ≤ σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ) (hslow : ε < (1 - 2 * δ / (σ + δ)) ^ N) {η : ℝ} (_h0 : 0 ≤ η) (h1 : η ≤ 1) :
    ¬ ((1 - η) ^ N ≤ ε ∧ η * σ / (2 - η) ≤ δ) := by
  rintro ⟨hf, hs⟩
  have hle : η ≤ 2 * δ / (σ + δ) := (ripple_le_iff hσ hδ (by linarith)).1 hs
  have hmax1 : 2 * δ / (σ + δ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have : (1 - 2 * δ / (σ + δ)) ^ N ≤ (1 - η) ^ N :=
    pow_le_pow_left₀ (by linarith) (by linarith) N
  linarith

theorem two_rates_suffice {σ δ ε : ℝ} {N : ℕ} (hN : 1 ≤ N) (hε : 0 ≤ ε) (hσ : 0 ≤ σ)
    (hδ : 0 < δ) (hδσ : δ ≤ σ) :
    (1 - 1 : ℝ) ^ N ≤ ε ∧ (2 * δ / (σ + δ)) * σ / (2 - 2 * δ / (σ + δ)) ≤ δ := by
  have hmax1 : 2 * δ / (σ + δ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  refine ⟨by rw [sub_self, zero_pow (by omega)]; exact hε, ?_⟩
  exact (ripple_le_iff hσ hδ (by linarith)).2 le_rfl

/-- Non-vacuity: no single rate catches a change to half-error within 10 steps while
keeping the noise ripple under 1%. -/
theorem conflict_instance (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    ¬ ((1 - η) ^ 10 ≤ 1 / 2 ∧ η * 1 / (2 - η) ≤ 1 / 100) :=
  single_rate_conflict (by norm_num) (by norm_num) (by norm_num) (by norm_num) h0 h1

end FiveOrgans.TwoSpeed
