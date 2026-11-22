import FiveOrgans.BrakeDelayD
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Any delay caps the safe gain at 1

Signal `x (n + d + 1) = x (n + d) - k * x n`, delay `d ≥ 1`.

* `delayD_unbounded` — for every `d ≥ 1` and every gain `k > 1` some real trajectory is
  unbounded.
  Proof: `z^(d+1) - z^d + k` is monic with constant term `k`, so (Vieta, over `ℂ`) the
  product of its `d+1` roots has modulus `k > 1`; hence some root `λ` has `|λ| > 1`.
  `Re λⁿ` and `Im λⁿ` are real solutions; if both were bounded, `|λⁿ|` would be.
* `delay_caps_gain` — packaged with the no-delay fact: for `k ∈ (1, 2)` the undelayed brake
  `x (n+1) = (1-k) x n` is bounded from every start, but with any delay `d ≥ 1` some start
  diverges. With `BrakeDelayD.delayD_bounded_small`, the delay-`d` safe range has its edge in
  `[d^d/(d+1)^(d+1), 1]`.

Not proved: the exact edge `2 sin(π/(2(2d+1)))` for `d ≥ 3`, and divergence from a *specific*
start (the theorem gives some start; for `d = 1, 2` the start `(0,…,0,1)` is shown in
`BrakeDelay`, `BrakeDelay2`).
-/

namespace FiveOrgans.BrakeDelayUnstable
open Polynomial

theorem norm_prod_le_one (s : Multiset ℂ) (h : ∀ z ∈ s, ‖z‖ ≤ 1) : ‖s.prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, norm_mul]
    have ha := h a (Multiset.mem_cons_self a s)
    have hs := ih (fun z hz => h z (Multiset.mem_cons_of_mem hz))
    nlinarith [norm_nonneg a, norm_nonneg s.prod]

/-- The characteristic polynomial has a root outside the unit disc when `k > 1`. -/
theorem big_root {d : ℕ} (hd : 1 ≤ d) {k : ℝ} (hk : 1 < k) :
    ∃ l : ℂ, 1 < ‖l‖ ∧ l ^ (d + 1) - l ^ d + (k : ℂ) = 0 := by
  set P : ℂ[X] := X ^ (d + 1) - X ^ d + C (k : ℂ) with hP
  have hdeg : (X ^ d - C (k : ℂ) : ℂ[X]).degree < (X ^ (d + 1) : ℂ[X]).degree := by
    rw [degree_X_pow]
    calc (X ^ d - C (k : ℂ) : ℂ[X]).degree ≤ d := by
          refine (degree_sub_le _ _).trans (max_le (degree_X_pow_le d) ?_)
          exact degree_C_le.trans (by exact_mod_cast Nat.zero_le d)
      _ < (d + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_self d
  have hm : P.Monic := by
    have : P = X ^ (d + 1) - (X ^ d - C (k : ℂ)) := by rw [hP]; ring
    rw [this]
    exact (monic_X_pow (d + 1)).sub_of_left hdeg
  have hc : P.coeff 0 = (k : ℂ) := by
    simp [hP, coeff_X_pow, show d ≠ 0 by omega, show (0 : ℕ) ≠ d by omega]
  have hv := (IsAlgClosed.splits P).coeff_zero_eq_prod_roots_of_monic hm
  rw [hc] at hv
  have hnorm : ‖P.roots.prod‖ = k := by
    have h1 := congrArg norm hv
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h1
    exact h1.symm
  by_contra hno
  push Not at hno
  have hle : ‖P.roots.prod‖ ≤ 1 := norm_prod_le_one _ (fun z hz => by
    have hr : P.IsRoot z := (mem_roots hm.ne_zero).mp hz
    by_contra hz1
    push Not at hz1
    apply hno z hz1
    simpa [hP] using hr)
  linarith

/-- **Any delay `d ≥ 1` with gain `k > 1` admits an unbounded trajectory.** -/
theorem delayD_unbounded {d : ℕ} (hd : 1 ≤ d) {k : ℝ} (hk : 1 < k) :
    ∃ x : ℕ → ℝ, (∀ n, x (n + d + 1) = x (n + d) - k * x n) ∧ ∀ B, ∃ n, B < |x n| := by
  obtain ⟨l, hl, hroot⟩ := big_root hd hk
  have hpow : ∀ n, l ^ (n + d + 1) = l ^ (n + d) - (k : ℂ) * l ^ n := by
    intro n
    have : l ^ (n + d + 1) - l ^ (n + d) + (k : ℂ) * l ^ n
        = l ^ n * (l ^ (d + 1) - l ^ d + (k : ℂ)) := by ring
    rw [hroot, mul_zero] at this
    linear_combination this
  have hre : ∀ n, (l ^ (n + d + 1)).re = (l ^ (n + d)).re - k * (l ^ n).re := by
    intro n; rw [hpow n, Complex.sub_re, Complex.re_ofReal_mul]
  have him : ∀ n, (l ^ (n + d + 1)).im = (l ^ (n + d)).im - k * (l ^ n).im := by
    intro n; rw [hpow n, Complex.sub_im, Complex.im_ofReal_mul]
  by_contra hno
  push Not at hno
  obtain ⟨B1, hB1⟩ := hno (fun n => (l ^ n).re) hre
  obtain ⟨B2, hB2⟩ := hno (fun n => (l ^ n).im) him
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B1 + B2) hl
  have h := Complex.norm_le_abs_re_add_abs_im (l ^ n)
  rw [norm_pow] at h
  linarith [hB1 n, hB2 n]

/-- Undelayed brake `x (n+1) = (1-k) x n` is bounded from every start for `0 < k < 2`. -/
theorem nodelay_bounded {k : ℝ} (hk0 : 0 < k) (hk2 : k < 2) {x : ℕ → ℝ}
    (hrec : ∀ n, x (n + 1) = (1 - k) * x n) : ∀ n, |x n| ≤ |x 0| := by
  intro n
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    rw [hrec, abs_mul]
    have : |1 - k| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg (x n)]

/-- **Delay caps the safe gain.** Every `k ∈ (1,2)` is safe without delay, unsafe with any
delay `d ≥ 1`. -/
theorem delay_caps_gain {d : ℕ} (hd : 1 ≤ d) {k : ℝ} (hk1 : 1 < k) (hk2 : k < 2) :
    (∀ x : ℕ → ℝ, (∀ n, x (n + 1) = (1 - k) * x n) → ∀ n, |x n| ≤ |x 0|) ∧
    (∃ x : ℕ → ℝ, (∀ n, x (n + d + 1) = x (n + d) - k * x n) ∧ ∀ B, ∃ n, B < |x n|) :=
  ⟨fun _ h => nodelay_bounded (by linarith) hk2 h, delayD_unbounded hd hk1⟩

/-- Any sequence obeying the one-step-delay recurrence is the `dx` trajectory from its start. -/
theorem eq_dx {k : ℝ} {x : ℕ → ℝ} (hrec : ∀ n, x (n + 2) = x (n + 1) - k * x n) (n : ℕ) :
    x n = BrakeDelay.dx k (x 0) (x 1) n ∧ x (n + 1) = BrakeDelay.dx k (x 0) (x 1) (n + 1) := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [show n + 1 + 1 = n + 2 from rfl, hrec, BrakeDelay.dx_succ_succ, ih.1, ih.2]

/-- **The one-step window, complete.** For `k > 0`: bounded from every start iff `k ≤ 1`;
above 1 every nonzero start diverges. (Edge `k = 1` included: bounded.) -/
theorem delay1_window {k : ℝ} (hk0 : 0 < k) :
    (k ≤ 1 → ∀ x : ℕ → ℝ, (∀ n, x (n + 2) = x (n + 1) - k * x n) →
        ∃ B, ∀ n, |x n| ≤ B) ∧
    (1 < k → ∀ x₀ x₁ : ℝ, (x₀ ≠ 0 ∨ x₁ ≠ 0) → ∀ B, ∃ n, B < |BrakeDelay.dx k x₀ x₁ n|) := by
  refine ⟨fun hk x hrec => ?_, fun hk x₀ x₁ h B => BrakeDelay.delayed_unbounded hk h B⟩
  rcases le_or_gt k (1 / 4) with h | h
  · exact BrakeDelayD.delay1_bounded_small hk0 h hrec
  · obtain ⟨B, hB⟩ := BrakeDelay.delayed_bounded h hk (x 0) (x 1)
    exact ⟨B, fun n => (eq_dx hrec n).1 ▸ hB n⟩

end FiveOrgans.BrakeDelayUnstable
