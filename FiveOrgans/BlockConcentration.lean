import FiveOrgans.CrossScaleTest
import FiveOrgans.RowConcentration
import FiveOrgans.RandomCount

/-!
# Block-level δ: the φ test only pays for macro states, and counts may be random

`CrossScaleTest` bounds each micro row's full ℓ¹ error, `rowErr ≤ δ`, and `RowConcentration`
pays `2^m` (`m` = number of micro states) for that. But the test only ever looks at **block
rows** (`blk`). This module works with the block error directly.

Deterministic part:
* `blkErr φ P P' x = Σ_y |blk φ P x y − blk φ P' x y|`; `blkErr_le` — it is `≤ rowErr`.
* `defect_transfer_blk`, `certified_transfer_blk`, `data_test_blk`, `split_rejects_blk`,
  `split_refutes_lumpable_blk` — the `CrossScaleTest` results with `blkErr` in place of `rowErr`.

Probability part (successors of each state from an independent table, as in `RowConcentration`):
* `blk_tail` — **`P(blkErr ≥ ε) ≤ 2^|Y| · exp(−N ε²/2)`**: the block row of the empirical law is the
  empirical law of the mapped draws `φ(Z i)`, so the Weissman bound applies on `Y`.
* `blk_rows_random` — **every state, random counts:** counts `N x ω ∈ {1,…,T}` may depend on the
  data in any way; `P(∃ x, blkErr_x ≥ δ(N x)) ≤ Σ_x Σ_{n ≤ T} 2^|Y| exp(−n δ(n)²/2)`.
* `blk_delta_solves`, `blk_rows_alpha` — with
  `δ(n)² = (2/n)(|Y| log 2 + log(m T/α))` the total is at most `α`.

Gain: the exponent in the cover term drops from `m log 2` to `|Y| log 2`. For 6 micro states in
2 blocks, 6 log 2 → 2 log 2. Still assumed: the random-table (time-homogeneous Markov) model.
-/

namespace FiveOrgans.BlockConcentration
open Finset Classical FiveOrgans.CrossScaleMarkov FiveOrgans.CrossScaleTest

section Det
variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- ℓ¹ error of the block row of `x`. -/
noncomputable def blkErr (φ : X → Y) (P P' : X → X → ℝ) (x : X) : ℝ :=
  ∑ y', |blk φ P x y' - blk φ P' x y'|

theorem blkErr_le (φ : X → Y) (P P' : X → X → ℝ) (x : X) : blkErr φ P P' x ≤ rowErr P P' x :=
  blk_dist φ P P' x

theorem defect_transfer_blk (φ : X → Y) (P P' : X → X → ℝ) (Q : Y → Y → ℝ) (x : X) :
    defect φ P Q x ≤ defect φ P' Q x + blkErr φ P P' x := by
  unfold defect blkErr
  calc ∑ y', |blk φ P x y' - Q (φ x) y'|
      ≤ ∑ y', (|blk φ P x y' - blk φ P' x y'| + |blk φ P' x y' - Q (φ x) y'|) :=
        sum_le_sum fun y' _ => abs_sub_le _ _ _
    _ = _ := by rw [sum_add_distrib, add_comm]

/-- **Certified transfer with block errors.** -/
theorem certified_transfer_blk {φ : X → Y} {P Ph : X → X → ℝ} {Q : Y → Y → ℝ}
    (hP : ∀ x x', 0 ≤ P x x') (hrow : ∀ x, ∑ x', P x x' ≤ 1)
    (hQ : ∀ y y', 0 ≤ Q y y') (hQrow : ∀ y, ∑ y', Q y y' ≤ 1) {δ η : ℝ}
    (hδ : ∀ x, blkErr φ P Ph x ≤ δ) (hη : ∀ x, defect φ Ph Q x ≤ η)
    (K : Set Y) (n : ℕ) (x : X) :
    |sv P (φ ⁻¹' K) n x - sv Q K n (φ x)| ≤ n * (η + δ) :=
  sv_approx_lump hP hrow hQ hQrow (fun x => by
    have h1 := defect_transfer_blk φ P Ph Q x
    have h2 := hη x
    have h3 := hδ x
    unfold defect blk at h1 h2
    linarith) K n x

/-- **The data test with block errors.** -/
theorem data_test_blk {φ : X → Y} {P Ph : X → X → ℝ} (r : Y → X)
    (hP : ∀ x x', 0 ≤ P x x') (hrow : ∀ x, ∑ x', P x x' ≤ 1)
    (hPh : ∀ x x', 0 ≤ Ph x x') (hPhrow : ∀ x, ∑ x', Ph x x' ≤ 1) {δ η : ℝ}
    (hδ : ∀ x, blkErr φ P Ph x ≤ δ) (hη : ∀ x, spread φ Ph r x ≤ η)
    (K : Set Y) (n : ℕ) (x : X) :
    |sv P (φ ⁻¹' K) n x - sv (Qhat φ Ph r) K n (φ x)| ≤ n * (η + δ) :=
  certified_transfer_blk hP hrow (fun y y' => blk_nonneg φ hPh (r y) y')
    (fun y => (blk_sum φ Ph (r y)).trans_le (hPhrow (r y))) hδ hη K n x

/-- **Certified rejection with block errors.** -/
theorem split_rejects_blk {φ : X → Y} {P Ph : X → X → ℝ} {δ η : ℝ} {x₁ x₂ : X}
    (hφ : φ x₁ = φ x₂) (h1 : blkErr φ P Ph x₁ ≤ δ) (h2 : blkErr φ P Ph x₂ ≤ δ)
    (hgap : 2 * δ + 2 * η < ∑ y', |blk φ Ph x₁ y' - blk φ Ph x₂ y'|) (Q : Y → Y → ℝ) :
    η < defect φ P Q x₁ ∨ η < defect φ P Q x₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨d1, d2⟩ := hcon
  have hpt : ∀ y', |blk φ Ph x₁ y' - blk φ Ph x₂ y'|
      ≤ |blk φ P x₁ y' - blk φ Ph x₁ y'| + |blk φ P x₁ y' - Q (φ x₁) y'|
        + |blk φ P x₂ y' - Q (φ x₂) y'| + |blk φ P x₂ y' - blk φ Ph x₂ y'| := by
    intro y'
    rw [hφ, abs_sub_le_iff]
    constructor <;>
    linarith [le_abs_self (blk φ P x₁ y' - blk φ Ph x₁ y'),
      neg_abs_le (blk φ P x₁ y' - blk φ Ph x₁ y'),
      le_abs_self (blk φ P x₁ y' - Q (φ x₂) y'), neg_abs_le (blk φ P x₁ y' - Q (φ x₂) y'),
      le_abs_self (blk φ P x₂ y' - Q (φ x₂) y'), neg_abs_le (blk φ P x₂ y' - Q (φ x₂) y'),
      le_abs_self (blk φ P x₂ y' - blk φ Ph x₂ y'),
      neg_abs_le (blk φ P x₂ y' - blk φ Ph x₂ y')]
  have hs := sum_le_sum fun y' (_ : y' ∈ univ) => hpt y'
  simp only [sum_add_distrib] at hs
  unfold blkErr at h1 h2
  unfold defect at d1 d2
  linarith

theorem split_refutes_lumpable_blk {φ : X → Y} {P Ph : X → X → ℝ} {δ : ℝ} {x₁ x₂ : X}
    (hφ : φ x₁ = φ x₂) (h1 : blkErr φ P Ph x₁ ≤ δ) (h2 : blkErr φ P Ph x₂ ≤ δ)
    (hgap : 2 * δ < ∑ y', |blk φ Ph x₁ y' - blk φ Ph x₂ y'|) :
    ¬ ∃ Q, Lumpable φ P Q := by
  rintro ⟨Q, hQ⟩
  rcases split_rejects_blk (η := 0) hφ h1 h2 (by linarith) Q with h | h <;>
    rw [lumpable_defect_zero hQ] at h <;> exact lt_irrefl _ h

end Det

section Prob
open MeasureTheory ProbabilityTheory Real FiveOrgans.RowConcentration FiveOrgans.RandomCount

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X Y : Type*} [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [Fintype Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]

omit [MeasurableSpace X] [DiscreteMeasurableSpace X] [Fintype Y] [MeasurableSpace Y]
  [DiscreteMeasurableSpace Y] in
theorem ind_map (φ : X → Y) (y : Y) (z : X) :
    ind {y} (φ z) = ind (univ.filter (fun x => φ x = y)) z := by
  unfold ind; split_ifs <;> simp_all

omit [MeasurableSpace Ω] [MeasurableSpace X] [DiscreteMeasurableSpace X] [Fintype Y]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y] in
theorem emp_map (φ : X → Y) (Z : ℕ → Ω → X) (N : ℕ) (ω : Ω) (y : Y) :
    emp (fun i ω => φ (Z i ω)) N ω y = ∑ x ∈ univ.filter (fun x => φ x = y), emp Z N ω x := by
  unfold emp
  rw [← sum_div, sum_comm]
  congr 1
  exact sum_congr rfl fun i _ => by rw [ind_map, ind_eq_sum]

/-- **Block concentration:** one row, `N` fixed. -/
theorem blk_tail (φ : X → Y) {Z : ℕ → Ω → X} (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z μ)
    {p : X → ℝ} (hlaw : ∀ i a, μ[fun ω => ind {a} (Z i ω)] = p a) (hp1 : ∑ a, p a = 1)
    {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ y, |∑ x ∈ univ.filter (fun x => φ x = y), p x
        - ∑ x ∈ univ.filter (fun x => φ x = y), emp Z N ω x|}
      ≤ 2 ^ Fintype.card Y * exp (-(N * ε ^ 2) / 2) := by
  let W : ℕ → Ω → Y := fun i ω => φ (Z i ω)
  let q : Y → ℝ := fun y => ∑ x ∈ univ.filter (fun x => φ x = y), p x
  have hW : ∀ i, Measurable (W i) := fun i => (Measurable.of_discrete (f := φ)).comp (hZ i)
  have hindW : iIndepFun W μ := hind.comp (fun _ => φ) (fun _ => Measurable.of_discrete)
  have hlawW : ∀ i y, μ[fun ω => ind {y} (W i ω)] = q y := fun i y => by
    simp only [W, q, ind_map]
    exact mean_ind (hZ i) (hlaw i) _
  have hq1 : ∑ y, q y = 1 := by simp only [q]; rw [Finset.sum_fiberwise univ φ p, hp1]
  refine le_trans (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _))
    (l1_tail hW hindW hlawW hq1 hN hε)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine hω.trans_eq (sum_congr rfl fun y _ => ?_)
  rw [abs_sub_comm, emp_map]

/-- **All rows, random counts.** -/
theorem blk_rows_random (φ : X → Y) {Z : X → ℕ → Ω → X} (hZ : ∀ x i, Measurable (Z x i))
    (hind : ∀ x, iIndepFun (Z x) μ) {P : X → X → ℝ}
    (hlaw : ∀ x i a, μ[fun ω => ind {a} (Z x i ω)] = P x a) (hP1 : ∀ x, ∑ a, P x a = 1)
    {T : ℕ} (N : X → Ω → ℕ) (hN : ∀ x ω, N x ω ∈ Icc 1 T) (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) :
    μ.real (⋃ x ∈ (univ : Finset X),
        {ω | δ (N x ω) ≤ blkErr φ P (fun x x' => emp (Z x) (N x ω) ω x') x})
      ≤ ∑ _x : X, ∑ n ∈ Icc 1 T, 2 ^ Fintype.card Y * exp (-(n * δ n ^ 2) / 2) := by
  refine (measureReal_biUnion_finset_le _ _).trans (sum_le_sum fun x _ => ?_)
  let bad : ℕ → Set Ω := fun n =>
    {ω | δ n ≤ ∑ y, |∑ x' ∈ univ.filter (fun x' => φ x' = y), P x x'
        - ∑ x' ∈ univ.filter (fun x' => φ x' = y), emp (Z x) n ω x'|}
  have h := random_index_le (μ := μ) bad (Icc 1 T) (N x) (hN x)
  refine le_trans (measureReal_mono (fun ω hω => hω) (measure_ne_top _ _))
    (h.trans (sum_le_sum fun n hn => ?_))
  have : 0 < n := by have := (mem_Icc.1 hn).1; omega
  exact blk_tail φ (hZ x) (hind x) (hlaw x) (hP1 x) this (hδ n)

/-- The block radius solves the per-term bound. -/
theorem blk_delta_solves {k n : ℕ} (hn : 0 < n) {c a : ℝ} (hc : 0 < c) (ha : 0 < a) {δ : ℝ}
    (hδ : δ ^ 2 = 2 / n * (k * log 2 + log (c / a))) :
    2 ^ k * exp (-(n * δ ^ 2) / 2) = a / c := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have he : -(n * δ ^ 2) / 2 = -(k * log 2) - log (c / a) := by
    rw [hδ]; field_simp; ring
  rw [he, exp_sub, exp_neg, exp_log (by positivity), ← log_rpow (by norm_num : (0 : ℝ) < 2),
    exp_log (by positivity), Real.rpow_natCast]
  field_simp

/-- **Calibrated block test with random counts:** error probability `≤ α`. -/
theorem blk_rows_alpha (φ : X → Y) {Z : X → ℕ → Ω → X} (hZ : ∀ x i, Measurable (Z x i))
    (hind : ∀ x, iIndepFun (Z x) μ) {P : X → X → ℝ}
    (hlaw : ∀ x i a, μ[fun ω => ind {a} (Z x i ω)] = P x a) (hP1 : ∀ x, ∑ a, P x a = 1)
    (hX : 0 < Fintype.card X) {T : ℕ} (hT : 0 < T) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (N : X → Ω → ℕ) (hN : ∀ x ω, N x ω ∈ Icc 1 T) :
    μ.real (⋃ x ∈ (univ : Finset X),
        {ω | √(2 / (N x ω : ℝ) * (Fintype.card Y * log 2
              + log (Fintype.card X * T / α))) ≤
          blkErr φ P (fun x x' => emp (Z x) (N x ω) ω x') x}) ≤ α := by
  set c : ℝ := Fintype.card X * T with hcdef
  have hc1 : 1 ≤ c := by
    have h1 : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast hX
    have h2 : (1 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have hc : 0 < c := by linarith
  have hlog : 0 ≤ Fintype.card Y * log 2 + log (c / α) := by
    have : 1 ≤ c / α := by rw [le_div_iff₀ hα]; linarith
    have := log_nonneg this
    have : 0 ≤ (Fintype.card Y : ℝ) * log 2 := mul_nonneg (by positivity) (log_nonneg (by norm_num))
    linarith
  have h := blk_rows_random φ hZ hind hlaw hP1 N hN
    (fun n => √(2 / (n : ℝ) * (Fintype.card Y * log 2 + log (c / α)))) (fun _ => sqrt_nonneg _)
  refine h.trans (le_of_eq ?_)
  have hterm : ∀ n ∈ Icc 1 T, 2 ^ Fintype.card Y
      * exp (-(n * √(2 / (n : ℝ) * (Fintype.card Y * log 2 + log (c / α))) ^ 2) / 2) = α / c := by
    intro n hn
    have hn0 : 0 < n := by have := (mem_Icc.1 hn).1; omega
    exact blk_delta_solves hn0 hc hα
      (sq_sqrt (mul_nonneg (div_nonneg zero_le_two (Nat.cast_nonneg n)) hlog))
  rw [sum_congr rfl fun x _ => sum_congr rfl hterm]
  simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, card_univ, nsmul_eq_mul]
  rw [hcdef]
  have : (T : ℝ) ≠ 0 := by positivity
  have : (Fintype.card X : ℝ) ≠ 0 := by positivity
  field_simp

end Prob

end FiveOrgans.BlockConcentration
