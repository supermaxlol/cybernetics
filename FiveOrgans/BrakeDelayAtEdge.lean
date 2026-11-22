import FiveOrgans.BrakeDelayExact
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.ComputeDegree

/-!
# Exactly at the delay edge `k = k_d`: every trajectory is bounded

`BrakeDelayExact` proves the window `0 < k < k_d` (every trajectory → 0) and `k > k_d` (some
trajectory unbounded) for `x(n+d+1) = x(n+d) − k·x(n)`, `d ≥ 1`. `BrakeDelayEdge` exhibits one
bounded non-decaying trajectory at `k = k_d`. This module settles the edge itself.

* `lam_root` — `λ = e^{iθ_d}` is a characteristic root at `k = k_d`, and so is `conj λ`.
* `roots_edge` — every characteristic root with `|z| ≥ 1` is `λ` or `conj λ`.
* `count_le_one` — the unit roots are **simple** (`p′(λ) = λ^{d−1}((d+1)λ − d) ≠ 0`).
* `roots_decomp` — the root multiset is `λ, conj λ` plus roots strictly inside the unit disc.
* `bps_of_roots_inside` — factors with roots inside the disc preserve summability (shift-operator
  argument, no spectral theory).
* `exact_edge_bounded` — **at `k = k_d` every real trajectory is bounded.**
* `edge_bounded_window` — so `0 < k ≤ k_d` ⟹ bounded, `k > k_d` ⟹ some trajectory unbounded:
  the closed window is exactly the bounded regime.

Scope: the linear delay recurrence only, exactly as in `BrakeDelayExact`.
-/

namespace FiveOrgans.BrakeDelayAtEdge
open Real Polynomial Finset FiveOrgans.BrakeDelayEdge FiveOrgans.BrakeDelayExact
open scoped ComplexConjugate

/-! ### Sequences with bounded partial sums of norms -/

/-- Bounded partial sums of norms (absolute summability, stated without `tsum`). -/
def BPS (f : ℕ → ℂ) : Prop := ∃ Z, ∀ N, ∑ n ∈ range N, ‖f n‖ ≤ Z

/-- A first-order factor with root inside the disc preserves `BPS`. -/
theorem bps_step {μ : ℂ} (hμ : ‖μ‖ < 1) {w z : ℕ → ℂ} (hz : BPS z)
    (hw : ∀ n, z n = w (n + 1) - μ * w n) : BPS w := by
  obtain ⟨Z, hZ⟩ := hz
  refine ⟨(‖w 0‖ + Z) / (1 - ‖μ‖), fun N => ?_⟩
  have h1 : ∀ n, ‖w (n + 1)‖ ≤ ‖μ‖ * ‖w n‖ + ‖z n‖ := fun n => by
    have : w (n + 1) = μ * w n + z n := by rw [hw n]; ring
    rw [this, ← norm_mul]; exact norm_add_le _ _
  have hS : ∑ n ∈ range (N + 1), ‖w n‖ ≤ ‖w 0‖ + ‖μ‖ * ∑ n ∈ range N, ‖w n‖ + Z := by
    rw [sum_range_succ', mul_sum]
    have := sum_le_sum fun n (_ : n ∈ range N) => h1 n
    rw [sum_add_distrib] at this
    linarith [hZ N]
  have hmono : ∑ n ∈ range N, ‖w n‖ ≤ ∑ n ∈ range (N + 1), ‖w n‖ := by
    rw [sum_range_succ]; linarith [norm_nonneg (w N)]
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- A first-order factor with a unit root keeps the solution bounded. -/
theorem unit_bound {μ : ℂ} (hμ : ‖μ‖ = 1) {w z : ℕ → ℂ} (hz : BPS z)
    (hw : ∀ n, z n = w (n + 1) - μ * w n) : ∃ B, ∀ n, ‖w n‖ ≤ B := by
  obtain ⟨Z, hZ⟩ := hz
  have key : ∀ n, ‖w n‖ ≤ ‖w 0‖ + ∑ j ∈ range n, ‖z j‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : w (n + 1) = μ * w n + z n := by rw [hw n]; ring
      rw [e, sum_range_succ]
      calc ‖μ * w n + z n‖ ≤ ‖μ‖ * ‖w n‖ + ‖z n‖ := by rw [← norm_mul]; exact norm_add_le _ _
        _ ≤ _ := by rw [hμ, one_mul]; linarith
  exact ⟨‖w 0‖ + Z, fun n => (key n).trans (by linarith [hZ n])⟩

/-! ### The shift operator -/

/-- Left shift on sequences. -/
def sh : Module.End ℂ (ℕ → ℂ) where
  toFun y n := y (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sh_pow (j : ℕ) (y : ℕ → ℂ) : (sh ^ j) y = fun n => y (n + j) := by
  induction j generalizing y with
  | zero => funext n; rw [pow_zero, Module.End.one_apply]; rfl
  | succ j ih => funext n; rw [pow_succ, Module.End.mul_apply, ih]; rfl

theorem aeval_lin (a : ℂ) (w : ℕ → ℂ) :
    aeval sh (X - C a) w = fun n => w (n + 1) - a * w n := by
  rw [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply]
  rfl

/-- **Factors with roots inside the disc preserve absolute summability.** -/
theorem bps_of_roots_inside (R : Multiset ℂ) :
    (∀ μ ∈ R, ‖μ‖ < 1) → ∀ y : ℕ → ℂ, BPS (aeval sh (R.map fun a => X - C a).prod y) → BPS y := by
  induction R using Multiset.induction_on with
  | empty => intro _ y h; simpa using h
  | cons μ R ih =>
    intro hR y h
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_apply, aeval_lin] at h
    have hw := bps_step (hR μ (Multiset.mem_cons_self μ R)) h (fun _ => rfl)
    exact ih (fun ν hν => hR ν (Multiset.mem_cons_of_mem hν)) y hw

/-! ### The characteristic polynomial at the edge -/

/-- `λ = e^{iθ_d}`. -/
noncomputable def lam (d : ℕ) : ℂ := Complex.exp ((θ d : ℂ) * Complex.I)

theorem lam_norm (d : ℕ) : ‖lam d‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem lam_conj_norm (d : ℕ) : ‖conj (lam d)‖ = 1 := by rw [Complex.norm_conj, lam_norm]

theorem lam_root {d : ℕ} (hd : 1 ≤ d) :
    lam d ^ (d + 1) - lam d ^ d + (kEdge d : ℂ) = 0 := by
  have h := half_turn d
  have h6 := half_le d hd
  have hθ := θ_pos d
  have e1 : (d : ℝ) * θ d = π / 2 - θ d / 2 := by linarith
  have e2 : ((d : ℝ) + 1) * θ d = θ d / 2 + π / 2 := by linarith
  have hc : 0 < cos (θ d / 2) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hS : sin (((d : ℝ) + 1) * θ d) ≠ 0 := by rw [e2, sin_add_pi_div_two]; exact hc.ne'
  have hρ : ρf d (θ d) = 1 := by
    unfold ρf; rw [e1, e2, sin_pi_div_two_sub, sin_add_pi_div_two, div_self hc.ne']
  have := param_root d hS
  rw [hρ, kf_edge hd, Complex.ofReal_one, one_mul] at this
  exact this

theorem lam_conj_root {d : ℕ} (hd : 1 ≤ d) :
    conj (lam d) ^ (d + 1) - conj (lam d) ^ d + (kEdge d : ℂ) = 0 := by
  have := congrArg conj (lam_root hd)
  rw [map_add, map_sub, map_pow, map_pow, Complex.conj_ofReal, map_zero] at this
  exact this

theorem lam_ne {d : ℕ} (hd : 1 ≤ d) : lam d ≠ conj (lam d) := by
  intro h
  have hθ := θ_pos d
  have h6 := half_le d hd
  have hs : 0 < sin (θ d) := sin_pos_of_pos_of_lt_pi hθ (by linarith [pi_pos])
  have := congrArg Complex.im h
  rw [Complex.conj_im, lam, Complex.exp_ofReal_mul_I_im] at this
  linarith

/-- Interior of the sector: no root with `|z| ≥ 1` and `|arg z| < θ_d` (any `k > 0`). -/
theorem sector_absurd {d : ℕ} (hd : 1 ≤ d) {k r t : ℝ} {z : ℂ} (hk0 : 0 < k)
    (hz : z ^ (d + 1) - z ^ d + (k : ℂ) = 0) (hr : 1 ≤ r)
    (hpolar : z = (r : ℂ) * Complex.exp (((2 * t : ℝ)) * Complex.I))
    (htlt : t < θ d / 2) (htgt : -(θ d / 2) < t) : False := by
  have hθ := θ_pos d
  have hθ6 := half_le d hd
  -- powers in polar form
  have hzpow : ∀ n : ℕ, z ^ n = ((r ^ n : ℝ) : ℂ) * Complex.exp (((n * (2 * t) : ℝ)) * Complex.I) := by
    intro n; rw [hpolar]; exact polar_pow r (2 * t) n
  have hre_n : ∀ n : ℕ, (z ^ n).re = r ^ n * cos (n * (2 * t)) := fun n => by
    rw [hzpow, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have him_n : ∀ n : ℕ, (z ^ n).im = r ^ n * sin (n * (2 * t)) := fun n => by
    rw [hzpow, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hrpos : 0 < r := by linarith
  have hrd : 0 < r ^ d := pow_pos hrpos d
  have hR : r ^ (d + 1) * cos ((2 * d + 1) * t + t) - r ^ d * cos ((2 * d + 1) * t - t) + k = 0 := by
    have h1 := hre_n (d + 1); have h2 := hre_n d
    rw [show ((d + 1 : ℕ) : ℝ) * (2 * t) = (2 * d + 1) * t + t by push_cast; ring] at h1
    rw [show (d : ℝ) * (2 * t) = (2 * d + 1) * t - t by ring] at h2
    have := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at this
    rw [h1, h2] at this; exact this
  have hI : r ^ (d + 1) * sin ((2 * d + 1) * t + t) - r ^ d * sin ((2 * d + 1) * t - t) = 0 := by
    have h1 := him_n (d + 1); have h2 := him_n d
    rw [show ((d + 1 : ℕ) : ℝ) * (2 * t) = (2 * d + 1) * t + t by push_cast; ring] at h1
    rw [show (d : ℝ) * (2 * t) = (2 * d + 1) * t - t by ring] at h2
    have := congrArg Complex.im hz
    simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.zero_im,
      add_zero] at this
    rw [h1, h2] at this; exact this
  have hIm : r * sin ((2 * d + 1) * t + t) = sin ((2 * d + 1) * t - t) := by
    have : r ^ d * (r * sin ((2 * d + 1) * t + t) - sin ((2 * d + 1) * t - t)) = 0 := by
      linear_combination hI
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hturn := half_turn d
  have hdpos : (0 : ℝ) < 2 * d + 1 := by positivity
  rcases lt_trichotomy t 0 with htn | ht0 | htp
  · -- t < 0: the imaginary part is strictly positive
    have hu_gt : -(π / 2) < (2 * d + 1) * t := by
      have := mul_lt_mul_of_pos_left htgt hdpos
      linarith
    have hu_neg : (2 * d + 1) * t < 0 := mul_neg_of_pos_of_neg hdpos htn
    have sU : sin ((2 * d + 1) * t) < 0 :=
      sin_neg_of_neg_of_neg_pi_lt hu_neg (by linarith [pi_pos])
    have cU : 0 < cos ((2 * d + 1) * t) := cos_pos_of_mem_Ioo ⟨hu_gt, by linarith [pi_pos]⟩
    have sT : sin t < 0 := sin_neg_of_neg_of_neg_pi_lt htn (by linarith [pi_pos])
    have cT : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith, by linarith [pi_pos]⟩
    rw [sin_add, sin_sub] at hIm
    have e1 : (r - 1) * (sin ((2 * d + 1) * t) * cos t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (mul_neg_of_neg_of_pos sU cT).le
    have e2 : (1 + r) * (cos ((2 * d + 1) * t) * sin t) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (mul_neg_of_pos_of_neg cU sT)
    have hsum : (r - 1) * (sin ((2 * d + 1) * t) * cos t) + (1 + r) * (cos ((2 * d + 1) * t) * sin t)
        = 0 := by linear_combination hIm
    linarith
  · -- t = 0: z is real and `≥ 1`, so `z^d (1 - z) ≤ 0 < k`
    subst ht0
    simp only [mul_zero, add_zero, sub_zero, cos_zero, mul_one] at hR
    have : r ^ (d + 1) = r ^ d * r := pow_succ r d
    have := mul_le_mul_of_nonneg_left hr hrd.le
    linarith
  · -- t > 0: the imaginary part is strictly negative
    have hu_lt : (2 * d + 1) * t < π / 2 := by
      have := mul_lt_mul_of_pos_left htlt hdpos
      linarith
    have hu_pos : 0 < (2 * d + 1) * t := mul_pos hdpos htp
    have sU : 0 < sin ((2 * d + 1) * t) := sin_pos_of_pos_of_lt_pi hu_pos (by linarith [pi_pos])
    have cU : 0 < cos ((2 * d + 1) * t) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hu_lt⟩
    have sT : 0 < sin t := sin_pos_of_pos_of_lt_pi htp (by linarith [pi_pos])
    have cT : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
    rw [sin_add, sin_sub] at hIm
    have e1 : 0 ≤ (r - 1) * (sin ((2 * d + 1) * t) * cos t) :=
      mul_nonneg (by linarith) (mul_pos sU cT).le
    have e2 : 0 < (1 + r) * (cos ((2 * d + 1) * t) * sin t) := mul_pos (by linarith) (mul_pos cU sT)
    have hsum : (r - 1) * (sin ((2 * d + 1) * t) * cos t) + (1 + r) * (cos ((2 * d + 1) * t) * sin t)
        = 0 := by linear_combination hIm
    linarith

/-- **At the edge the only roots on or outside the unit circle are `λ` and `conj λ`.** -/
theorem roots_edge {d : ℕ} (hd : 1 ≤ d) {z : ℂ}
    (hz : z ^ (d + 1) - z ^ d + (kEdge d : ℂ) = 0) (hr1 : 1 ≤ ‖z‖) :
    z = lam d ∨ z = conj (lam d) := by
  have hk0 : 0 < kEdge d := edge_pos d
  obtain ⟨r, hrdef⟩ : ∃ r, ‖z‖ = r := ⟨_, rfl⟩
  have hr : 1 ≤ r := hrdef ▸ hr1
  obtain ⟨t, ht⟩ : ∃ t, Complex.arg z = 2 * t := ⟨Complex.arg z / 2, by ring⟩
  have hpolar : z = (r : ℂ) * Complex.exp (((2 * t : ℝ)) * Complex.I) := by
    rw [← ht, ← hrdef]; exact (Complex.norm_mul_exp_arg_mul_I z).symm
  have ht_lo : -(π / 2) < t := by have := Complex.neg_pi_lt_arg z; rw [ht] at this; linarith
  have ht_hi : t ≤ π / 2 := by have := Complex.arg_le_pi z; rw [ht] at this; linarith
  have hf : z ^ d * (1 - z) = (kEdge d : ℂ) := by linear_combination (-1 : ℂ) * hz
  have hnorm : r ^ d * ‖1 - z‖ = kEdge d := by
    have := congrArg norm hf
    rw [norm_mul, norm_pow, hrdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk0] at this
    exact this
  have hrd1 : 1 ≤ r ^ d := one_le_pow₀ hr
  have hle : ‖1 - z‖ ≤ kEdge d := by
    have := mul_le_mul_of_nonneg_right hrd1 (norm_nonneg (1 - z)); linarith
  have hzre : z.re = r * cos (2 * t) := by
    rw [hpolar, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hzim : z.im = r * sin (2 * t) := by
    rw [hpolar, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hn2 : ‖1 - z‖ ^ 2 = (1 - r * cos (2 * t)) ^ 2 + (r * sin (2 * t)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, hzre, hzim]; ring
  have hc2 : cos (2 * t) = 1 - 2 * sin t ^ 2 := by
    rw [cos_two_mul]; linarith [sin_sq_add_cos_sq t]
  have hpy := sin_sq_add_cos_sq (2 * t)
  have hid : (1 - r * cos (2 * t)) ^ 2 + (r * sin (2 * t)) ^ 2 - 4 * sin t ^ 2
      = (r - 1) * (r + 1 - 2 * cos (2 * t)) := by linear_combination r ^ 2 * hpy - 2 * hc2
  have hlow : 4 * sin t ^ 2 ≤ ‖1 - z‖ ^ 2 := by
    have hnn : 0 ≤ (r - 1) * (r + 1 - 2 * cos (2 * t)) :=
      mul_nonneg (by linarith) (by linarith [cos_le_one (2 * t)])
    rw [hn2]; linarith
  have hθ := θ_pos d
  have hθ6 := half_le d hd
  have hs0 : 0 < sin (θ d / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have hk2 : ‖1 - z‖ ^ 2 ≤ kEdge d ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hkk : kEdge d ^ 2 = 4 * sin (θ d / 2) ^ 2 := by unfold kEdge; ring
  have hsq : sin t ^ 2 ≤ sin (θ d / 2) ^ 2 := by linarith
  have htle : t ≤ θ d / 2 := by
    by_contra h; push Not at h
    have h1 := sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [pi_pos]) ht_hi h
    have := pow_lt_pow_left₀ h1 hs0.le (by norm_num : (2 : ℕ) ≠ 0)
    linarith
  have htge : -(θ d / 2) ≤ t := by
    by_contra h; push Not at h
    have h1 := sin_lt_sin_of_lt_of_le_pi_div_two ht_lo.le (by linarith [pi_pos]) h
    rw [sin_neg] at h1
    have := pow_lt_pow_left₀ (show sin (θ d / 2) < -sin t by linarith) hs0.le
      (by norm_num : (2 : ℕ) ≠ 0)
    rw [neg_sq] at this
    linarith
  -- on the boundary rays the modulus is forced to 1
  have hbdry : sin t ^ 2 = sin (θ d / 2) ^ 2 → r = 1 := by
    intro hst
    have hpos : 0 < sin t ^ 2 := by rw [hst]; exact pow_pos hs0 2
    have hA : 0 < r + 1 - 2 * cos (2 * t) := by rw [hc2]; linarith
    by_contra hne
    have hr1' : 0 < r - 1 := sub_pos.2 (lt_of_le_of_ne hr (Ne.symm hne))
    have := mul_pos hr1' hA
    rw [hn2] at hk2
    linarith
  rcases htle.lt_or_eq with htlt | hteq
  · rcases htge.lt_or_eq with htgt | hteq'
    · exact (sector_absurd hd hk0 hz hr hpolar htlt htgt).elim
    · right
      have hr1' : r = 1 := hbdry (by rw [← hteq', sin_neg, neg_sq])
      rw [hpolar, hr1', ← hteq', lam, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
        Complex.conj_I, Complex.ofReal_one, one_mul]
      congr 1; push_cast; ring
  · left
    have hr1' : r = 1 := hbdry (by rw [hteq])
    rw [hpolar, hr1', hteq, lam, Complex.ofReal_one, one_mul]
    congr 2; ring

/-- The characteristic polynomial at the edge. -/
noncomputable def pC (d : ℕ) : ℂ[X] := X ^ (d + 1) - X ^ d + C ((kEdge d : ℝ) : ℂ)

theorem pC_monic (d : ℕ) : (pC d).Monic := by unfold pC; monicity!

theorem pC_ne (d : ℕ) : pC d ≠ 0 := (pC_monic d).ne_zero

theorem pC_eval (d : ℕ) (z : ℂ) : (pC d).eval z = z ^ (d + 1) - z ^ d + (kEdge d : ℂ) := by
  simp [pC]

theorem deriv_ne {d : ℕ} (hd : 1 ≤ d) {z : ℂ} (hz : ‖z‖ = 1) :
    ((d : ℂ) + 1) * z ^ d - (d : ℂ) * z ^ (d - 1) ≠ 0 := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  intro h
  have hz0 : z ^ e ≠ 0 := pow_ne_zero _ (by rintro rfl; simp at hz)
  have h2 : ((e : ℂ) + 2) * z = (e : ℂ) + 1 := by
    have : z ^ e * (((e : ℂ) + 2) * z - ((e : ℂ) + 1)) = 0 := by
      push_cast at h; linear_combination h
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hz0
    · linear_combination h0
  have := congrArg norm h2
  rw [norm_mul, hz, mul_one] at this
  have e1 : ‖(e : ℂ) + 2‖ = (e : ℝ) + 2 := by
    rw [show (e : ℂ) + 2 = ((e + 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have e2 : ‖(e : ℂ) + 1‖ = (e : ℝ) + 1 := by
    rw [show (e : ℂ) + 1 = ((e + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [e1, e2] at this
  linarith

/-- **Unit roots are simple.** -/
theorem count_le_one {d : ℕ} (hd : 1 ≤ d) {z : ℂ} (hz : ‖z‖ = 1) :
    (pC d).roots.count z ≤ 1 := by
  classical
  rw [count_roots]
  by_contra h
  push Not at h
  have := ((one_lt_rootMultiplicity_iff_isRoot (pC_ne d)).1 h).2
  rw [IsRoot.def] at this
  simp [pC, derivative_X_pow] at this
  exact deriv_ne hd hz (by linear_combination this)

theorem roots_decomp {d : ℕ} (hd : 1 ≤ d) : ∃ R : Multiset ℂ,
    (pC d).roots = lam d ::ₘ conj (lam d) ::ₘ R ∧ ∀ μ ∈ R, ‖μ‖ < 1 := by
  classical
  have hne := pC_ne d
  have h1 : lam d ∈ (pC d).roots :=
    (mem_roots hne).2 (by rw [IsRoot.def, pC_eval]; exact lam_root hd)
  have h2' : conj (lam d) ∈ (pC d).roots :=
    (mem_roots hne).2 (by rw [IsRoot.def, pC_eval]; exact lam_conj_root hd)
  have h2 : conj (lam d) ∈ (pC d).roots.erase (lam d) :=
    (Multiset.mem_erase_of_ne (lam_ne hd).symm).2 h2'
  obtain ⟨R, hdec⟩ : ∃ R, (pC d).roots = lam d ::ₘ conj (lam d) ::ₘ R :=
    ⟨((pC d).roots.erase (lam d)).erase (conj (lam d)), by
      rw [Multiset.cons_erase h2, Multiset.cons_erase h1]⟩
  refine ⟨R, hdec, fun μ hμ => ?_⟩
  by_contra hge
  push Not at hge
  have hμr : μ ∈ (pC d).roots := by rw [hdec]; simp [hμ]
  have hroot := (mem_roots hne).1 hμr
  rw [IsRoot.def, pC_eval] at hroot
  have hpos := Multiset.count_pos.2 hμ
  rcases roots_edge hd hroot hge with rfl | rfl
  · have := count_le_one hd (lam_norm d)
    rw [hdec, Multiset.count_cons_self, Multiset.count_cons] at this
    split_ifs at this <;> omega
  · have := count_le_one hd (lam_conj_norm d)
    rw [hdec, Multiset.count_cons, Multiset.count_cons_self] at this
    split_ifs at this <;> omega

/-! ### Every trajectory is bounded at the edge -/

/-- **Exactly at `k = k_d` every trajectory is bounded.** -/
theorem exact_edge_bounded {d : ℕ} (hd : 1 ≤ d) {x : ℕ → ℝ}
    (hrec : ∀ n, x (n + d + 1) = x (n + d) - kEdge d * x n) : ∃ B, ∀ n, |x n| ≤ B := by
  obtain ⟨R, hdec, hR⟩ := roots_decomp hd
  set l := lam d with hl
  set lc := conj (lam d) with hlc
  set Xc : ℕ → ℂ := fun n => (x n : ℂ) with hXc
  have hp0 : aeval sh (pC d) Xc = 0 := by
    funext n
    simp only [pC, map_add, map_sub, map_pow, aeval_X, aeval_C, LinearMap.add_apply,
      LinearMap.sub_apply, sh_pow, Module.algebraMap_end_apply, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hXc]
    rw [← add_assoc, hrec n]; push_cast; ring
  have hfac : pC d = (R.map fun a => X - C a).prod * ((X - C l) * (X - C lc)) := by
    conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq (pC_monic d)
      IsAlgClosed.card_roots_eq_natDegree, hdec]
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons]
    ring
  have hq : aeval sh (R.map fun a => X - C a).prod (aeval sh ((X - C l) * (X - C lc)) Xc) = 0 := by
    rw [← Module.End.mul_apply, ← map_mul, ← hfac]; exact hp0
  have hz : BPS (aeval sh ((X - C l) * (X - C lc)) Xc) :=
    bps_of_roots_inside R hR _ (by rw [hq]; exact ⟨0, fun N => by simp⟩)
  set w : ℕ → ℂ := fun n => Xc (n + 1) - lc * Xc n with hw
  set w' : ℕ → ℂ := fun n => Xc (n + 1) - l * Xc n with hw'
  have hzw : aeval sh ((X - C l) * (X - C lc)) Xc = fun n => w (n + 1) - l * w n := by
    rw [map_mul, Module.End.mul_apply, aeval_lin, aeval_lin]
  have hzw' : aeval sh ((X - C l) * (X - C lc)) Xc = fun n => w' (n + 1) - lc * w' n := by
    rw [mul_comm, map_mul, Module.End.mul_apply, aeval_lin, aeval_lin]
  obtain ⟨B1, hB1⟩ := unit_bound (lam_norm d) hz (fun n => congrFun hzw n)
  obtain ⟨B2, hB2⟩ := unit_bound (lam_conj_norm d) hz (fun n => congrFun hzw' n)
  have hdiff : ∀ n, (l - lc) * Xc n = w n - w' n := fun n => by simp only [hw, hw']; ring
  have hlne : l - lc ≠ 0 := sub_ne_zero.2 (lam_ne hd)
  refine ⟨(B1 + B2) / ‖l - lc‖, fun n => ?_⟩
  have hn : |x n| = ‖Xc n‖ := by simp [hXc]
  rw [hn, le_div_iff₀ (norm_pos_iff.2 hlne), mul_comm, ← norm_mul, hdiff]
  exact (norm_sub_le _ _).trans (add_le_add (hB1 n) (hB2 n))

/-- **The closed window.** For `0 < k ≤ k_d` every trajectory is bounded; for `k > k_d` some
trajectory is unbounded. -/
theorem edge_bounded_window {d : ℕ} (hd : 1 ≤ d) {k : ℝ} (hk0 : 0 < k) :
    (k ≤ kEdge d ↔ ∀ x : ℕ → ℝ, (∀ n, x (n + d + 1) = x (n + d) - k * x n) →
      ∃ B, ∀ n, |x n| ≤ B) := by
  constructor
  · intro hk x hrec
    rcases hk.lt_or_eq with hlt | heq
    · exact exact_edge_stable hd hk0 hlt hrec
    · subst heq; exact exact_edge_bounded hd hrec
  · intro hb
    by_contra h
    push Not at h
    obtain ⟨x, hrec, hun⟩ := exact_edge_unstable hd h
    obtain ⟨B, hB⟩ := hb x hrec
    obtain ⟨n, hn⟩ := hun B
    linarith [hB n]

end FiveOrgans.BrakeDelayAtEdge
