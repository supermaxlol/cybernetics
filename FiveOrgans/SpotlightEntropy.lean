import FiveOrgans.SpotlightNoisy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Field

/-!
# The Spotlight with an information cost (rational inattention) and random error

`Spotlight` assumes attention is free to aim. Rational inattention charges for precise aiming:
the agent picks a distribution `w` over items (`w i ≥ 0`, `Σ w = 1`) and pays `λ > 0` times
the information it uses, measured here by the entropy reduction from uniform. Up to a constant
the objective is

  `J λ v w = Σ w i v i − λ Σ w i log w i`   (`Real.log 0 = 0`, so `0 log 0 = 0`).

* `gibbs_term` — `w (log s − log w) ≤ s − w` for `w ≥ 0`, `s > 0` (from `log x ≤ x − 1`).
* `softmax_optimal` — **the optimum is the softmax** `s i = exp(v i/λ)/Z`:
  `J λ v w ≤ λ log Z = J λ v s` for every distribution `w`.
* `entropy_le_log` — `−Σ w log w ≤ log n`.
* `softmax_payoff_ge` — the softmax's task payoff is at least `v_max − λ log n`. **An
  information cost λ costs at most `λ log n` of payoff**, and the cost-free spotlight is the
  `λ → 0` limit.
* `softmax_spreads` — at every `λ > 0` the optimum puts positive weight on every item, so a
  priced spotlight is never a perfect spotlight.
* `expected_regret` — **random estimation error:** if on outcome `ω` (probability `p ω`) the
  estimates are within `e ω` of the truth and the spotlight follows the estimates, the expected
  payoff is at least `C v_b − 2C E[e]` for every item `b`.

Scope: entropy as the information measure (the standard rational-inattention choice), finite
items, finite outcome space. Which measure real agents pay is EMP?.
-/

namespace FiveOrgans.SpotlightEntropy
open Finset Real FiveOrgans.Spotlight FiveOrgans.SpotlightNoisy

variable {n : ℕ}

theorem gibbs_term {w s : ℝ} (hw : 0 ≤ w) (hs : 0 < s) : w * (log s - log w) ≤ s - w := by
  rcases hw.eq_or_lt with h | h
  · subst h; simp; linarith
  · have := log_le_sub_one_of_pos (div_pos hs h)
    rw [log_div hs.ne' h.ne'] at this
    have e : w * (s / w - 1) = s - w := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left this h.le]

/-- Rational-inattention objective. -/
noncomputable def J (lam : ℝ) (v w : Fin n → ℝ) : ℝ := ∑ i, w i * v i - lam * ∑ i, w i * log (w i)

noncomputable def Z (lam : ℝ) (v : Fin n → ℝ) : ℝ := ∑ i, exp (v i / lam)

noncomputable def softmax (lam : ℝ) (v : Fin n → ℝ) : Fin n → ℝ := fun i => exp (v i / lam) / Z lam v

theorem Z_pos [NeZero n] (lam : ℝ) (v : Fin n → ℝ) : 0 < Z lam v :=
  sum_pos (fun i _ => exp_pos _) univ_nonempty

theorem softmax_pos [NeZero n] (lam : ℝ) (v : Fin n → ℝ) (i : Fin n) : 0 < softmax lam v i :=
  div_pos (exp_pos _) (Z_pos lam v)

theorem softmax_sum [NeZero n] (lam : ℝ) (v : Fin n → ℝ) : ∑ i, softmax lam v i = 1 := by
  unfold softmax; rw [← sum_div]; exact div_self (Z_pos lam v).ne'

theorem log_softmax [NeZero n] {lam : ℝ} (_hl : 0 < lam) (v : Fin n → ℝ) (i : Fin n) :
    log (softmax lam v i) = v i / lam - log (Z lam v) := by
  unfold softmax; rw [log_div (exp_pos _).ne' (Z_pos lam v).ne', log_exp]

/-- **Softmax is optimal under an entropy information cost.** -/
theorem softmax_optimal [NeZero n] {lam : ℝ} (hl : 0 < lam) (v w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    J lam v w ≤ lam * log (Z lam v) ∧ J lam v (softmax lam v) = lam * log (Z lam v) := by
  have key : ∀ u : Fin n → ℝ, ∑ i, u i = 1 →
      J lam v u = lam * log (Z lam v) + lam * ∑ i, u i * (log (softmax lam v i) - log (u i)) := by
    intro u hu
    unfold J
    simp_rw [log_softmax hl]
    have : ∑ i, u i * (v i / lam - log (Z lam v) - log (u i))
        = (∑ i, u i * v i) / lam - log (Z lam v) * ∑ i, u i - ∑ i, u i * log (u i) := by
      rw [sum_div, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [this, hu]; field_simp; ring
  constructor
  · rw [key w hw1]
    have hg : ∑ i, w i * (log (softmax lam v i) - log (w i)) ≤ 0 := by
      calc ∑ i, w i * (log (softmax lam v i) - log (w i))
          ≤ ∑ i, (softmax lam v i - w i) :=
            sum_le_sum fun i _ => gibbs_term (hw i) (softmax_pos lam v i)
        _ = 0 := by rw [sum_sub_distrib, softmax_sum, hw1, sub_self]
    nlinarith
  · rw [key _ (softmax_sum lam v)]; simp

/-- Entropy is at most `log n`. -/
theorem entropy_le_log [NeZero n] (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    -∑ i, w i * log (w i) ≤ log n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have h := sum_le_sum fun i (_ : i ∈ univ) => gibbs_term (hw i) (by positivity : (0 : ℝ) < 1 / n)
  rw [sum_sub_distrib, hw1] at h
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have e : ∑ i, w i * (log (1 / (n : ℝ)) - log (w i)) = -log n - ∑ i, w i * log (w i) := by
    rw [one_div, log_inv]
    simp_rw [mul_sub]; rw [sum_sub_distrib, ← sum_mul, hw1]; ring
  rw [e] at h
  have : (n : ℝ) * (1 / n) = 1 := by field_simp
  linarith

/-- **An information cost λ costs at most `λ log n` of payoff.** -/
theorem softmax_payoff_ge [NeZero n] {lam : ℝ} (hl : 0 < lam) (v : Fin n → ℝ) (b : Fin n) :
    v b - lam * log n ≤ ∑ i, softmax lam v i * v i := by
  have hopt := (softmax_optimal hl v (softmax lam v) (fun i => (softmax_pos lam v i).le)
    (softmax_sum lam v)).2
  have hZ : v b / lam ≤ log (Z lam v) := by
    rw [← log_exp (v b / lam)]
    exact log_le_log (exp_pos _) (by
      unfold Z; exact single_le_sum (f := fun i => exp (v i / lam)) (fun i _ => (exp_pos _).le) (mem_univ b))
  have hH := entropy_le_log (softmax lam v) (fun i => (softmax_pos lam v i).le) (softmax_sum lam v)
  unfold J at hopt
  have h1 : v b ≤ lam * log (Z lam v) := by
    have := mul_le_mul_of_nonneg_left hZ hl.le; rwa [mul_div_cancel₀ _ hl.ne'] at this
  nlinarith

/-- **A priced spotlight is never a perfect spotlight:** every item gets positive weight. -/
theorem softmax_spreads [NeZero n] (lam : ℝ) (v : Fin n → ℝ) (i : Fin n) :
    0 < softmax lam v i := softmax_pos lam v i

/-- **Random estimation error:** expected payoff of following noisy estimates. -/
theorem expected_regret {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (hp1 : ∑ ω, p ω = 1) {C : ℝ} (hC : 0 ≤ C) {v : Fin n → ℝ} (u : Ω → Fin n → ℝ)
    (e : Ω → ℝ) (hu : ∀ ω i, |u ω i - v i| ≤ e ω) (j : Ω → Fin n)
    (hj : ∀ ω i, u ω i ≤ u ω (j ω)) (b : Fin n) :
    C * v b - 2 * C * ∑ ω, p ω * e ω ≤ ∑ ω, p ω * (C * v (j ω)) := by
  have h : ∀ ω, p ω * (C * v b - 2 * C * e ω) ≤ p ω * (C * v (j ω)) := fun ω =>
    mul_le_mul_of_nonneg_left (by nlinarith [noisy_pick_regret (hu ω) (hj ω) b]) (hp ω)
  calc C * v b - 2 * C * ∑ ω, p ω * e ω = ∑ ω, p ω * (C * v b - 2 * C * e ω) := by
        simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, hp1, mul_sum]
        congr 1 <;> [ring; exact sum_congr rfl fun ω _ => by ring]
    _ ≤ _ := sum_le_sum fun ω _ => h ω

end FiveOrgans.SpotlightEntropy
