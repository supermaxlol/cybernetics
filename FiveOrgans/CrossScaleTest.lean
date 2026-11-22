import FiveOrgans.CrossScaleMarkov

/-!
# A data-side test for φ: certified transfer and certified rejection

`CrossScaleMarkov.sv_approx_lump` says: if the *true* micro kernel `P` is within `η` of being
lumpable onto `Q` through `φ`, micro and macro survival differ by at most `n η`. The true `P` is
never observed. What is observed is an estimate `Ph` (transition counts divided by visits).
This module splits the question into a part that is computed from data and a part that is a
sampling assumption:

* `rowErr P Ph x = Σ_x' |P x x' − Ph x x'|`, the estimation error of row `x` (ℓ¹). **Not
  computable**; it is bounded by `δ` through a concentration inequality under a sampling model.
* `defect φ Ph Q x = Σ_y' |Ph(x → block y') − Q(φ x, y')|`, the lumpability defect of the
  estimate. **Computable from data.**

Results:
* `blk_dist` — moving to blocks never increases ℓ¹ error.
* `defect_transfer` — `defect P ≤ defect Ph + rowErr`.
* `certified_transfer` — **if every estimated defect is `≤ η` and every row error is `≤ δ`,
  the true micro survival is within `n (η + δ)` of macro survival, at every horizon.**
* `Qhat`, `spread`, `data_test` — the macro kernel can itself be read off the data (block row of
  a representative state per block). Then `η` is the within-block spread of estimated block
  rows, and the whole left side of the test is computed from logs.
* `split_rejects` — **rejection:** if two micro states with the same image have estimated block
  rows more than `2δ + 2η` apart (ℓ¹), then **no** macro kernel `Q` is within `η` of the true
  chain at both states. `split_refutes_lumpable` — gap `> 2δ` refutes exact lumpability onto
  every `Q`.

What is not in Lean: the step "with probability ≥ 1 − α, every `rowErr ≤ δ`". That is a
statistical statement (e.g. the ℓ¹ deviation bound of Weissman et al. 2003 plus a union bound
over states, now proved in `RowConcentration`: `l1_tail`, `rows_tail`, `delta_solves`) and it needs a sampling model (time-homogeneous Markov data, enough visits per
state). `analysis/lumpability_test.py` computes `δ` that way, labelled as an assumption.
Passing the test certifies transfer *given* that sampling model; it does not make a real system
Markov, finite, or time-homogeneous. Which real system to test is EMP?.
-/

namespace FiveOrgans.CrossScaleTest
open Finset Classical FiveOrgans.CrossScaleMarkov

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Probability of jumping from `x` into the block `φ⁻¹{y'}`. -/
noncomputable def blk (φ : X → Y) (P : X → X → ℝ) (x : X) (y' : Y) : ℝ :=
  ∑ x' ∈ univ.filter (fun x' => φ x' = y'), P x x'

/-- ℓ¹ error of row `x` of an estimate. -/
noncomputable def rowErr (P P' : X → X → ℝ) (x : X) : ℝ := ∑ x', |P x x' - P' x x'|

/-- Lumpability defect at `x` (ℓ¹ distance of the block row from the macro row). -/
noncomputable def defect (φ : X → Y) (P : X → X → ℝ) (Q : Y → Y → ℝ) (x : X) : ℝ :=
  ∑ y', |blk φ P x y' - Q (φ x) y'|

theorem blk_sum (φ : X → Y) (P : X → X → ℝ) (x : X) : ∑ y', blk φ P x y' = ∑ x', P x x' :=
  Finset.sum_fiberwise univ φ (P x)

omit [Fintype Y] in
theorem blk_nonneg (φ : X → Y) {P : X → X → ℝ} (hP : ∀ x x', 0 ≤ P x x') (x : X) (y' : Y) :
    0 ≤ blk φ P x y' :=
  sum_nonneg fun x' _ => hP x x'

/-- Coarse-graining never increases ℓ¹ error. -/
theorem blk_dist (φ : X → Y) (P P' : X → X → ℝ) (x : X) :
    ∑ y', |blk φ P x y' - blk φ P' x y'| ≤ rowErr P P' x := by
  unfold blk rowErr
  calc ∑ y', |∑ x' ∈ univ.filter (fun x' => φ x' = y'), P x x'
          - ∑ x' ∈ univ.filter (fun x' => φ x' = y'), P' x x'|
      = ∑ y', |∑ x' ∈ univ.filter (fun x' => φ x' = y'), (P x x' - P' x x')| := by
        simp_rw [sum_sub_distrib]
    _ ≤ ∑ y', ∑ x' ∈ univ.filter (fun x' => φ x' = y'), |P x x' - P' x x'| :=
        sum_le_sum fun y' _ => abs_sum_le_sum_abs _ _
    _ = ∑ x', |P x x' - P' x x'| :=
        Finset.sum_fiberwise univ φ (fun x' => |P x x' - P' x x'|)

theorem defect_transfer (φ : X → Y) (P P' : X → X → ℝ) (Q : Y → Y → ℝ) (x : X) :
    defect φ P Q x ≤ defect φ P' Q x + rowErr P P' x := by
  have hb := blk_dist φ P P' x
  unfold defect
  calc ∑ y', |blk φ P x y' - Q (φ x) y'|
      ≤ ∑ y', (|blk φ P x y' - blk φ P' x y'| + |blk φ P' x y' - Q (φ x) y'|) :=
        sum_le_sum fun y' _ => abs_sub_le _ _ _
    _ = ∑ y', |blk φ P' x y' - Q (φ x) y'| + ∑ y', |blk φ P x y' - blk φ P' x y'| := by
        rw [sum_add_distrib, add_comm]
    _ ≤ ∑ y', |blk φ P' x y' - Q (φ x) y'| + rowErr P P' x := by linarith

/-- **Certified transfer.** Estimated defect `≤ η` everywhere and row error `≤ δ` everywhere
give a survival gap `≤ n (η + δ)` for the *true* chain. -/
theorem certified_transfer {φ : X → Y} {P Ph : X → X → ℝ} {Q : Y → Y → ℝ}
    (hP : ∀ x x', 0 ≤ P x x') (hrow : ∀ x, ∑ x', P x x' ≤ 1)
    (hQ : ∀ y y', 0 ≤ Q y y') (hQrow : ∀ y, ∑ y', Q y y' ≤ 1) {δ η : ℝ}
    (hδ : ∀ x, rowErr P Ph x ≤ δ) (hη : ∀ x, defect φ Ph Q x ≤ η)
    (K : Set Y) (n : ℕ) (x : X) :
    |sv P (φ ⁻¹' K) n x - sv Q K n (φ x)| ≤ n * (η + δ) :=
  sv_approx_lump hP hrow hQ hQrow (fun x => by
    have h1 := defect_transfer φ P Ph Q x
    have h2 := hη x
    have h3 := hδ x
    unfold defect blk at h1 h2
    linarith) K n x

/-- Macro kernel read off the data: the estimated block row of a representative `r y`. -/
noncomputable def Qhat (φ : X → Y) (Ph : X → X → ℝ) (r : Y → X) (y y' : Y) : ℝ :=
  blk φ Ph (r y) y'

/-- Within-block spread: how far `x`'s estimated block row is from its representative's. -/
noncomputable def spread (φ : X → Y) (Ph : X → X → ℝ) (r : Y → X) (x : X) : ℝ :=
  ∑ y', |blk φ Ph x y' - blk φ Ph (r (φ x)) y'|

theorem spread_eq_defect (φ : X → Y) (Ph : X → X → ℝ) (r : Y → X) (x : X) :
    spread φ Ph r x = defect φ Ph (Qhat φ Ph r) x := rfl

/-- **The data test.** Build `Qhat` from the estimate. If every within-block spread is `≤ η`
and every row error is `≤ δ`, true micro survival is within `n (η + δ)` of `Qhat` survival. -/
theorem data_test {φ : X → Y} {P Ph : X → X → ℝ} (r : Y → X)
    (hP : ∀ x x', 0 ≤ P x x') (hrow : ∀ x, ∑ x', P x x' ≤ 1)
    (hPh : ∀ x x', 0 ≤ Ph x x') (hPhrow : ∀ x, ∑ x', Ph x x' ≤ 1) {δ η : ℝ}
    (hδ : ∀ x, rowErr P Ph x ≤ δ) (hη : ∀ x, spread φ Ph r x ≤ η)
    (K : Set Y) (n : ℕ) (x : X) :
    |sv P (φ ⁻¹' K) n x - sv (Qhat φ Ph r) K n (φ x)| ≤ n * (η + δ) :=
  certified_transfer hP hrow (fun y y' => blk_nonneg φ hPh (r y) y')
    (fun y => (blk_sum φ Ph (r y)).trans_le (hPhrow (r y))) hδ hη K n x

/-- **Certified rejection.** Two micro states with the same image whose estimated block rows
are more than `2δ + 2η` apart: no macro kernel is within `η` of the true chain at both. -/
theorem split_rejects {φ : X → Y} {P Ph : X → X → ℝ} {δ η : ℝ} {x₁ x₂ : X}
    (hφ : φ x₁ = φ x₂) (h1 : rowErr P Ph x₁ ≤ δ) (h2 : rowErr P Ph x₂ ≤ δ)
    (hgap : 2 * δ + 2 * η < ∑ y', |blk φ Ph x₁ y' - blk φ Ph x₂ y'|) (Q : Y → Y → ℝ) :
    η < defect φ P Q x₁ ∨ η < defect φ P Q x₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨d1, d2⟩ := hcon
  have hpt : ∀ y', |blk φ Ph x₁ y' - blk φ Ph x₂ y'|
      ≤ |blk φ P x₁ y' - blk φ Ph x₁ y'| + |blk φ P x₁ y' - Q (φ x₁) y'|
        + |blk φ P x₂ y' - Q (φ x₂) y'| + |blk φ P x₂ y' - blk φ Ph x₂ y'| := by
    intro y'
    rw [hφ]
    rw [abs_sub_le_iff]
    constructor <;>
    linarith [le_abs_self (blk φ P x₁ y' - blk φ Ph x₁ y'),
      neg_abs_le (blk φ P x₁ y' - blk φ Ph x₁ y'),
      le_abs_self (blk φ P x₁ y' - Q (φ x₂) y'), neg_abs_le (blk φ P x₁ y' - Q (φ x₂) y'),
      le_abs_self (blk φ P x₂ y' - Q (φ x₂) y'), neg_abs_le (blk φ P x₂ y' - Q (φ x₂) y'),
      le_abs_self (blk φ P x₂ y' - blk φ Ph x₂ y'),
      neg_abs_le (blk φ P x₂ y' - blk φ Ph x₂ y')]
  have hs := sum_le_sum fun y' (_ : y' ∈ univ) => hpt y'
  simp only [sum_add_distrib] at hs
  have e1 := blk_dist φ P Ph x₁
  have e2 := blk_dist φ P Ph x₂
  unfold defect at d1 d2
  linarith

theorem lumpable_defect_zero {φ : X → Y} {P : X → X → ℝ} {Q : Y → Y → ℝ}
    (h : Lumpable φ P Q) (x : X) : defect φ P Q x = 0 := by
  unfold defect blk
  simp [h x]

/-- **Refuting exact lumpability from data:** a within-block gap `> 2δ` rules out every `Q`. -/
theorem split_refutes_lumpable {φ : X → Y} {P Ph : X → X → ℝ} {δ : ℝ} {x₁ x₂ : X}
    (hφ : φ x₁ = φ x₂) (h1 : rowErr P Ph x₁ ≤ δ) (h2 : rowErr P Ph x₂ ≤ δ)
    (hgap : 2 * δ < ∑ y', |blk φ Ph x₁ y' - blk φ Ph x₂ y'|) :
    ¬ ∃ Q, Lumpable φ P Q := by
  rintro ⟨Q, hQ⟩
  rcases split_rejects (η := 0) hφ h1 h2 (by linarith) Q with h | h <;>
    rw [lumpable_defect_zero hQ] at h <;> exact lt_irrefl _ h

end FiveOrgans.CrossScaleTest
