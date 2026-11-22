import FiveOrgans.BrakeDelayEdge
import FiveOrgans.BrakeDelayUnstable
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The exact delay edge for every delay `d ≥ 1`

Brake with delay `d`: `x (n+d+1) = x (n+d) − k x n`. `BrakeDelayD` proved boundedness for
`k ≤ d^d/(d+1)^(d+1)`, `BrakeDelayUnstable` proved an unbounded trajectory for `k > 1`, and
`BrakeDelayEdge` identified the candidate edge `kEdge d = 2 sin(π/(2(2d+1)))` with a bounded,
non-decaying trajectory on it. Exact windows were proved for `d = 1, 2` only. This module
closes the window for **every** `d ≥ 1`:

* `roots_inside` — for `0 < k < kEdge d`, every complex root of `z^(d+1) − z^d + k` has
  `‖z‖ < 1`. (From `‖1 − z‖ ≤ k` the argument is pinned to `|arg z| < θ_d`; the imaginary part
  of the equation then has a strict sign. Contradiction.)
* `eig_root`, `specRad_lt` — the companion matrix's eigenvalues are such roots, so its spectral
  radius is `< 1`.
* `exact_edge_stable` — **below the edge every real trajectory is bounded** (Gelfand's formula
  gives `‖Aⁿ‖ ≤ 1` eventually).
* `param_root`, `rho_gt`, `kf_edge` — for `α ∈ (θ_d, π/(d+1))` the point
  `ρ(α) e^{iα}` with `ρ = sin(dα)/sin((d+1)α) > 1` is a root for the gain
  `kf d α = ρ^d sin α / sin((d+1)α)`, and `kf d θ_d = kEdge d`.
* `exact_edge_unstable` — **above the edge some trajectory is unbounded** (intermediate value
  theorem on `kf`, then the real/imaginary parts of `zⁿ`).
* `exact_window` — both together.

At the edge itself `BrakeDelayEdge.edge_rec` gives a bounded trajectory that never decays.
That *every* trajectory is bounded exactly at `k = kEdge d` is proved in `BrakeDelayAtEdge`.
Scope: the linear delayed brake model only.
-/

namespace FiveOrgans.BrakeDelayExact
open Real FiveOrgans.BrakeDelayEdge
open scoped ENNReal NNReal Matrix

/-! ### Polar powers -/

theorem polar_pow (r α : ℝ) (n : ℕ) :
    ((r : ℂ) * Complex.exp (α * Complex.I)) ^ n
      = ((r ^ n : ℝ) : ℂ) * Complex.exp (((n * α : ℝ)) * Complex.I) := by
  rw [mul_pow, ← Complex.exp_nat_mul]; push_cast; ring_nf

theorem polar_pow_re (r α : ℝ) (n : ℕ) :
    (((r : ℂ) * Complex.exp (α * Complex.I)) ^ n).re = r ^ n * cos (n * α) := by
  rw [polar_pow, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem polar_pow_im (r α : ℝ) (n : ℕ) :
    (((r : ℂ) * Complex.exp (α * Complex.I)) ^ n).im = r ^ n * sin (n * α) := by
  rw [polar_pow, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-! ### Below the edge: all roots strictly inside the unit circle -/

/-- **Root location below the edge.** -/
theorem roots_inside {d : ℕ} (hd : 1 ≤ d) {k : ℝ} (hk0 : 0 < k) (hk : k < kEdge d) {z : ℂ}
    (hz : z ^ (d + 1) - z ^ d + (k : ℂ) = 0) : ‖z‖ < 1 := by
  by_contra hr
  push Not at hr
  obtain ⟨r, hrdef⟩ : ∃ r, ‖z‖ = r := ⟨_, rfl⟩
  rw [hrdef] at hr
  obtain ⟨t, ht⟩ : ∃ t, Complex.arg z = 2 * t := ⟨Complex.arg z / 2, by ring⟩
  have hpolar : z = (r : ℂ) * Complex.exp (((2 * t : ℝ)) * Complex.I) := by
    rw [← ht, ← hrdef]; exact (Complex.norm_mul_exp_arg_mul_I z).symm
  have ht_lo : -(π / 2) < t := by have := Complex.neg_pi_lt_arg z; rw [ht] at this; linarith
  have ht_hi : t ≤ π / 2 := by have := Complex.arg_le_pi z; rw [ht] at this; linarith
  -- modulus estimate: ‖1 - z‖ ≤ k
  have hf : z ^ d * (1 - z) = (k : ℂ) := by linear_combination (-1 : ℂ) * hz
  have hnorm : r ^ d * ‖1 - z‖ = k := by
    have := congrArg norm hf
    rw [norm_mul, norm_pow, hrdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk0] at this
    exact this
  have hrd1 : 1 ≤ r ^ d := one_le_pow₀ hr
  have hle : ‖1 - z‖ ≤ k := by
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
  have hlow : 4 * sin t ^ 2 ≤ ‖1 - z‖ ^ 2 := by
    have hid : (1 - r * cos (2 * t)) ^ 2 + (r * sin (2 * t)) ^ 2 - 4 * sin t ^ 2
        = (r - 1) * (r + 1 - 2 * cos (2 * t)) := by linear_combination r ^ 2 * hpy - 2 * hc2
    have hnn : 0 ≤ (r - 1) * (r + 1 - 2 * cos (2 * t)) :=
      mul_nonneg (by linarith) (by linarith [cos_le_one (2 * t)])
    rw [hn2]; linarith
  have hkE : k ^ 2 < (kEdge d) ^ 2 := pow_lt_pow_left₀ hk hk0.le (by norm_num)
  have hθ := θ_pos d
  have hθ6 := half_le d hd
  have hs0 : 0 < sin (θ d / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have hsq : sin t ^ 2 < sin (θ d / 2) ^ 2 := by
    have hk2 : ‖1 - z‖ ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    have : (kEdge d) ^ 2 = 4 * sin (θ d / 2) ^ 2 := by unfold kEdge; ring
    linarith
  have htlt : t < θ d / 2 := by
    by_contra h; push Not at h
    have := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) ht_hi h
    have := pow_le_pow_left₀ hs0.le this 2
    linarith
  have htgt : -(θ d / 2) < t := by
    by_contra h; push Not at h
    have := sin_le_sin_of_le_of_le_pi_div_two ht_lo.le (by linarith [pi_pos]) h
    rw [sin_neg] at this
    have := pow_le_pow_left₀ hs0.le (show sin (θ d / 2) ≤ -sin t by linarith) 2
    rw [neg_sq] at this
    linarith
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

/-! ### The companion matrix -/

/-- Companion matrix of the delayed brake: `(A v)_i = v_{i+1}` for `i < d`,
`(A v)_d = v_d − k v_0`. -/
noncomputable def comp (d : ℕ) (k : ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  fun i j => if (i : ℕ) < d then (if (j : ℕ) = i + 1 then 1 else 0)
    else (if (j : ℕ) = d then 1 else 0) - (if (j : ℕ) = 0 then (k : ℂ) else 0)

theorem sum_pick {n : ℕ} (v : Fin n → ℂ) (m : ℕ) (hm : m < n) (c : ℂ) :
    ∑ j : Fin n, (if (j : ℕ) = m then c else 0) * v j = c * v ⟨m, hm⟩ := by
  rw [Fintype.sum_eq_single ⟨m, hm⟩]
  · simp
  · intro j hj
    have : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
    simp [this]

variable {d : ℕ} {k : ℝ}

theorem comp_mulVec_lt (v : Fin (d + 1) → ℂ) (i : Fin (d + 1)) (hi : (i : ℕ) < d) :
    (comp d k *ᵥ v) i = v ⟨i + 1, by omega⟩ := by
  simp only [Matrix.mulVec, dotProduct, comp, hi, ite_true]
  rw [sum_pick v (i + 1) (by omega) 1, one_mul]

theorem comp_mulVec_last (hd : 1 ≤ d) (v : Fin (d + 1) → ℂ) :
    (comp d k *ᵥ v) (Fin.last d) = v (Fin.last d) - k * v 0 := by
  simp only [Matrix.mulVec, dotProduct, comp, Fin.val_last, lt_irrefl, ite_false, sub_mul,
    Finset.sum_sub_distrib]
  rw [sum_pick v d (by omega) 1, sum_pick v 0 (by omega) (k : ℂ), one_mul]
  rfl

theorem comp_step (hd : 1 ≤ d) {x : ℕ → ℝ} (hrec : ∀ n, x (n + d + 1) = x (n + d) - k * x n)
    (n : ℕ) :
    comp d k *ᵥ (fun i : Fin (d + 1) => ((x (n + i) : ℝ) : ℂ))
      = fun i : Fin (d + 1) => ((x (n + 1 + i) : ℝ) : ℂ) := by
  funext i
  by_cases hi : (i : ℕ) < d
  · rw [comp_mulVec_lt _ i hi]
    dsimp only
    rw [show n + (↑i + 1) = n + 1 + ↑i by omega]
  · have : i = Fin.last d := Fin.ext (by simp; omega)
    subst this
    rw [comp_mulVec_last hd]
    simp only [Fin.val_last, Fin.val_zero, add_zero]
    rw [show n + 1 + d = n + d + 1 by omega, hrec]
    push_cast; ring

theorem comp_pow (hd : 1 ≤ d) {x : ℕ → ℝ} (hrec : ∀ n, x (n + d + 1) = x (n + d) - k * x n)
    (n : ℕ) :
    (fun i : Fin (d + 1) => ((x (n + i) : ℝ) : ℂ))
      = (comp d k ^ n) *ᵥ (fun i : Fin (d + 1) => ((x i : ℝ) : ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ← ih, comp_step hd hrec n]

/-- **Every eigenvalue of the companion matrix is a root of `z^(d+1) − z^d + k`.** -/
theorem eig_root (hd : 1 ≤ d) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (comp d k)) :
    μ ^ (d + 1) - μ ^ d + (k : ℂ) = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hμ
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hμ
  rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
    Matrix.one_mulVec, sub_eq_zero] at hv
  have heig : ∀ i, (comp d k *ᵥ v) i = μ * v i := fun i => by
    rw [← hv]; rfl
  have hpow : ∀ i (hi : i ≤ d), v ⟨i, by omega⟩ = μ ^ i * v 0 := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have h1 := comp_mulVec_lt (k := k) v ⟨i, by omega⟩ (by simp; omega)
      rw [heig] at h1
      rw [← h1, ih (by omega), pow_succ]; ring
  have hv00 : v 0 ≠ 0 := by
    intro h0; apply hv0; funext i
    have := hpow i (by omega)
    simp only [h0, mul_zero, Fin.eta] at this
    simpa using this
  have hl := comp_mulVec_last (k := k) hd v
  rw [heig] at hl
  have hvd : v (Fin.last d) = μ ^ d * v 0 := hpow d le_rfl
  rw [hvd] at hl
  have : (μ ^ (d + 1) - μ ^ d + k) * v 0 = 0 := by linear_combination hl
  exact (mul_eq_zero.1 this).resolve_right hv00

section Gelfand

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem specRad_lt (hd : 1 ≤ d) (hk0 : 0 < k) (hk : k < kEdge d) :
    spectralRadius ℂ (comp d k) < 1 := by
  obtain ⟨μ, hμ, heq⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum.nonempty (comp d k))
  rw [← heq]
  have h := roots_inside hd hk0 hk (eig_root hd hμ)
  exact ENNReal.coe_lt_one_iff.2 (by rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]; exact h)

/-- **Below the edge every real trajectory is bounded.** -/
theorem exact_edge_stable (hd : 1 ≤ d) (hk0 : 0 < k) (hk : k < kEdge d) {x : ℕ → ℝ}
    (hrec : ∀ n, x (n + d + 1) = x (n + d) - k * x n) : ∃ B, ∀ n, |x n| ≤ B := by
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (specRad_lt hd hk0 hk)
  have hev := (tendsto_order.1
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (comp d k))).2 _ hr1
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  have hbound : ∀ n, ‖comp d k ^ n‖ ≤ ∑ m ∈ Finset.range (N + 1), ‖comp d k ^ m‖ + 1 := by
    intro n
    have hs : 0 ≤ ∑ m ∈ Finset.range (N + 1), ‖comp d k ^ m‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    rcases lt_or_ge n (N + 1) with h | h
    · have := Finset.single_le_sum (f := fun m => ‖comp d k ^ m‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.2 h)
      linarith
    · have hn1 : ‖comp d k ^ n‖ ≤ 1 := by
        by_contra hc; push Not at hc
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have h1 : (1 : ℝ≥0∞) ≤ (‖comp d k ^ n‖₊ : ℝ≥0∞) := by
          rw [ENNReal.one_le_coe_iff, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
          exact hc.le
        have h2 := ENNReal.one_le_rpow h1 (one_div_pos.2 hnpos)
        exact absurd ((hN n (by omega)).trans hr2) (not_lt.2 h2)
      linarith
  refine ⟨(∑ m ∈ Finset.range (N + 1), ‖comp d k ^ m‖ + 1) *
      ‖(fun i : Fin (d + 1) => ((x i : ℝ) : ℂ))‖, fun n => ?_⟩
  have h1 : |x n| ≤ ‖(fun i : Fin (d + 1) => ((x (n + i) : ℝ) : ℂ))‖ := by
    have := norm_le_pi_norm (fun i : Fin (d + 1) => ((x (n + i) : ℝ) : ℂ)) 0
    simpa [Complex.norm_real] using this
  rw [comp_pow hd hrec n] at h1
  calc |x n| ≤ _ := h1
    _ ≤ ‖comp d k ^ n‖ * ‖(fun i : Fin (d + 1) => ((x i : ℝ) : ℂ))‖ :=
        Matrix.linfty_opNorm_mulVec _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _)

end Gelfand

/-! ### Above the edge: an explicit root outside the unit circle -/

/-- A root of modulus `> 1` gives an unbounded real trajectory (as in `delayD_unbounded`). -/
theorem unbounded_of_root {l : ℂ} (hl : 1 < ‖l‖) (hroot : l ^ (d + 1) - l ^ d + (k : ℂ) = 0) :
    ∃ x : ℕ → ℝ, (∀ n, x (n + d + 1) = x (n + d) - k * x n) ∧ ∀ B, ∃ n, B < |x n| := by
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

/-- Root modulus along the parametrised branch. -/
noncomputable def ρf (d : ℕ) (α : ℝ) : ℝ := sin (d * α) / sin ((d + 1) * α)

/-- Gain at which `ρf d α · e^{iα}` is a root. -/
noncomputable def kf (d : ℕ) (α : ℝ) : ℝ := ρf d α ^ d * sin α / sin ((d + 1) * α)

theorem param_root (d : ℕ) {α : ℝ} (hS : sin (((d : ℝ) + 1) * α) ≠ 0) :
    ((ρf d α : ℂ) * Complex.exp (α * Complex.I)) ^ (d + 1)
      - ((ρf d α : ℂ) * Complex.exp (α * Complex.I)) ^ d + (kf d α : ℂ) = 0 := by
  have hρ : ρf d α * sin (((d : ℝ) + 1) * α) = sin (d * α) := div_mul_cancel₀ _ hS
  have hsa : sin α = sin (((d : ℝ) + 1) * α) * cos (d * α) - cos (((d : ℝ) + 1) * α) * sin (d * α) := by
    rw [← sin_sub]; congr 1; ring
  apply Complex.ext
  · simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.zero_re, polar_pow_re]
    push_cast
    unfold kf
    rw [hsa, ← hρ]
    field_simp
    ring
  · simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.zero_im, add_zero,
      polar_pow_im]
    push_cast
    rw [← hρ]; ring

theorem rho_gt (hd : 1 ≤ d) {α : ℝ} (h1 : θ d < α) (h2 : ((d : ℝ) + 1) * α < π) :
    0 < sin (((d : ℝ) + 1) * α) ∧ sin (((d : ℝ) + 1) * α) < sin (d * α) := by
  have hα : 0 < α := (θ_pos d).trans h1
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hS : 0 < sin (((d : ℝ) + 1) * α) := sin_pos_of_pos_of_lt_pi (by positivity) h2
  refine ⟨hS, ?_⟩
  have h2α : 2 * α ≤ ((d : ℝ) + 1) * α := by nlinarith [mul_nonneg (sub_nonneg.2 hd1) hα.le]
  have e := Real.sin_sub_sin ((d : ℝ) * α) (((d : ℝ) + 1) * α)
  rw [show ((d : ℝ) * α - ((d : ℝ) + 1) * α) / 2 = -(α / 2) by ring,
    show ((d : ℝ) * α + ((d : ℝ) + 1) * α) / 2 = (2 * d + 1) * α / 2 by ring, sin_neg] at e
  have hs : 0 < sin (α / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hturn := half_turn d
  have hlo : π / 2 < (2 * d + 1) * α / 2 := by
    have : ((d : ℝ) + 1 / 2) * θ d < ((d : ℝ) + 1 / 2) * α :=
      mul_lt_mul_of_pos_left h1 (by positivity)
    linarith
  have hhi : (2 * d + 1) * α / 2 < π + π / 2 := by linarith [pi_pos]
  have hc : cos ((2 * d + 1) * α / 2) < 0 := cos_neg_of_pi_div_two_lt_of_lt hlo hhi
  linarith [mul_pos hs (neg_pos.2 hc)]

theorem kf_edge (hd : 1 ≤ d) : kf d (θ d) = kEdge d := by
  have h := half_turn d
  have h6 := half_le d hd
  have hθ := θ_pos d
  have e1 : (d : ℝ) * θ d = π / 2 - θ d / 2 := by linarith
  have e2 : ((d : ℝ) + 1) * θ d = θ d / 2 + π / 2 := by linarith
  have hc : 0 < cos (θ d / 2) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hs2 : sin (θ d) = 2 * sin (θ d / 2) * cos (θ d / 2) := by
    have := sin_two_mul (θ d / 2)
    rw [show 2 * (θ d / 2) = θ d by ring] at this
    exact this
  unfold kf ρf kEdge
  rw [e1, e2, sin_pi_div_two_sub, sin_add_pi_div_two, div_self hc.ne', one_pow, one_mul, hs2,
    mul_div_assoc, div_self hc.ne', mul_one]

/-- **Above the edge some trajectory is unbounded.** -/
theorem exact_edge_unstable (hd : 1 ≤ d) (hk : kEdge d < k) :
    ∃ x : ℕ → ℝ, (∀ n, x (n + d + 1) = x (n + d) - k * x n) ∧ ∀ B, ∃ n, B < |x n| := by
  have hθ := θ_pos d
  have hθ6 := half_le d hd
  have hθπ : θ d < π := by linarith [pi_pos]
  have hsθ : 0 < sin (θ d) := sin_pos_of_pos_of_lt_pi hθ hθπ
  have hkpos : 0 < k := (edge_pos d).trans hk
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  obtain ⟨s, hs⟩ : ∃ s, s = min (sin (θ d) / (k + 1)) 1 := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; exact lt_min (div_pos hsθ (by linarith)) one_pos
  have hs1 : s ≤ 1 := by rw [hs]; exact min_le_right _ _
  have hs2 : s ≤ sin (θ d) / (k + 1) := by rw [hs]; exact min_le_left _ _
  obtain ⟨β, hβ⟩ : ∃ β, β = (π - s) / (d + 1) := ⟨_, rfl⟩
  have hβe : ((d : ℝ) + 1) * β = π - s := by rw [hβ]; field_simp
  have hturn := half_turn d
  have hdθ : ((d : ℝ) + 1) * θ d = π / 2 + θ d / 2 := by linarith
  have hθβ : θ d < β := by
    have : ((d : ℝ) + 1) * θ d < ((d : ℝ) + 1) * β := by
      rw [hdθ, hβe]; linarith [pi_gt_three]
    exact lt_of_mul_lt_mul_left this hd1.le
  have hβπ : ((d : ℝ) + 1) * β < π := by rw [hβe]; linarith
  have hβle : β ≤ π / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hdR) (hθ.trans hθβ).le]
  obtain ⟨hSβ, hρβ⟩ := rho_gt hd hθβ hβπ
  have hkfβ : k + 1 ≤ kf d β := by
    have hSle : sin (((d : ℝ) + 1) * β) ≤ s := by rw [hβe, sin_pi_sub]; exact sin_le hs0.le
    have hρ1 : 1 ≤ ρf d β := by unfold ρf; rw [le_div_iff₀ hSβ]; linarith
    have hsinβ : sin (θ d) ≤ sin β :=
      sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hβle hθβ.le
    unfold kf
    rw [le_div_iff₀ (by linarith)] at hs2
    calc k + 1 ≤ sin (θ d) / s := by rw [le_div_iff₀ hs0]; linarith
      _ ≤ sin (θ d) / sin (((d : ℝ) + 1) * β) := div_le_div_of_nonneg_left hsθ.le hSβ hSle
      _ ≤ ρf d β ^ d * sin β / sin (((d : ℝ) + 1) * β) := by
          apply div_le_div_of_nonneg_right _ hSβ.le
          calc sin (θ d) ≤ sin β := hsinβ
            _ = 1 * sin β := (one_mul _).symm
            _ ≤ ρf d β ^ d * sin β :=
                mul_le_mul_of_nonneg_right (one_le_pow₀ hρ1) (hsθ.le.trans hsinβ)
  have hne : ∀ x ∈ Set.Icc (θ d) β, sin (((d : ℝ) + 1) * x) ≠ 0 := fun x hx => by
    have : 0 < ((d : ℝ) + 1) * x := mul_pos hd1 (hθ.trans_le hx.1)
    exact (sin_pos_of_pos_of_lt_pi this
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hx.2 hd1.le) hβπ)).ne'
  have hc1 : ContinuousOn (fun x => sin (((d : ℝ) + 1) * x)) (Set.Icc (θ d) β) := by fun_prop
  have hρc : ContinuousOn (ρf d) (Set.Icc (θ d) β) :=
    (by fun_prop : ContinuousOn (fun x => sin ((d : ℝ) * x)) _).div hc1 hne
  have hcont : ContinuousOn (kf d) (Set.Icc (θ d) β) := by
    have : kf d = fun x => ρf d x ^ d * sin x / sin (((d : ℝ) + 1) * x) := rfl
    rw [this]
    exact ((hρc.pow d).mul (by fun_prop)).div hc1 hne
  have hmem : k ∈ Set.Icc (kf d (θ d)) (kf d β) := by
    rw [kf_edge hd]; exact ⟨hk.le, by linarith⟩
  obtain ⟨α, ⟨hα1, hα2⟩, hkα⟩ := intermediate_value_Icc hθβ.le hcont hmem
  have hαθ : θ d < α := lt_of_le_of_ne hα1 (fun h => by
    rw [← h, kf_edge hd] at hkα; linarith)
  have hαπ : ((d : ℝ) + 1) * α < π :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hα2 hd1.le) hβπ
  obtain ⟨hS, hρ⟩ := rho_gt hd hαθ hαπ
  have hρ1 : 1 < ρf d α := by unfold ρf; rw [lt_div_iff₀ hS]; linarith
  refine unbounded_of_root (l := (ρf d α : ℂ) * Complex.exp (α * Complex.I)) ?_ ?_
  · rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    exact hρ1
  · rw [← hkα]; exact param_root d hS.ne'

/-- **The exact delay window, every `d ≥ 1`.** Below `kEdge d` every trajectory is bounded;
above it some trajectory is unbounded. -/
theorem exact_window (hd : 1 ≤ d) (hk0 : 0 < k) :
    (k < kEdge d → ∀ x : ℕ → ℝ, (∀ n, x (n + d + 1) = x (n + d) - k * x n) →
        ∃ B, ∀ n, |x n| ≤ B) ∧
    (kEdge d < k → ∃ x : ℕ → ℝ, (∀ n, x (n + d + 1) = x (n + d) - k * x n) ∧
        ∀ B, ∃ n, B < |x n|) :=
  ⟨fun hk _ hrec => exact_edge_stable hd hk0 hk hrec, fun hk => exact_edge_unstable hd hk⟩

end FiveOrgans.BrakeDelayExact
