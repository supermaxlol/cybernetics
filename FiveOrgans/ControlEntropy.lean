import FiveOrgans.SensingRate
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Feedback and entropy: the Touchette–Lloyd bound

State `x`, controller state `c`, joint distribution `J x c`, actuation kernel `K c x y`.
`I(X;C)` is mutual information (`mi`), logs natural.

* `cond_chain`: `H(X,C) = H(C) + Σ_c p(c) H(X|c)`.
* `ent_mix_ge`: entropy is concave, so `H(X') ≥ Σ_c p(c) H(X'|c)`.
* `touchette_lloyd`: if every pure control lowers the entropy of **every** input distribution by at
  most `D`, then closed-loop control lowers entropy by at most `D + I(X;C)`.
* `openMax`, `touchette_lloyd_sup`: the same with `D` the supremum over inputs and controls.
* `mi_le_log_card`, `reduction_le_messages`: `I(X;C) ≤ log |C|`, so a controller with `M` states
  adds at most `log M` (the average-case partner of `SensingRate.forever_iff`).
* `mi_nonneg`: mutual information is nonnegative.
* `cnot_tight`: equality is attained (perfect feedback on one bit).
* `same_state_fails`: the bound is **false** if `D` is computed only at the current state. So the
  supremum over input distributions cannot be dropped.

Source: Touchette and Lloyd, PRL 84 (2000) 1156 and Physica A 331 (2004) 140 (Theorem 10). The
proof here is the conditional one of the 2004 paper. Scope: finite sets, one control step; the
controller state may be any random variable jointly distributed with the state. Entropy reduction is
not survival.
-/

namespace FiveOrgans.ControlEntropy
open FiveOrgans.CompressionInfo Finset Real

variable {X C Y : Type*} [Fintype X] [Fintype C] [Fintype Y]

theorem ent_eq (q : X → ℝ) : ent q = ∑ x, negMulLog (q x) := by
  unfold ent negMulLog; exact sum_congr rfl fun _ _ => by ring

/-- Marginal of the first coordinate. -/
noncomputable def mX (J : X → C → ℝ) (x : X) : ℝ := ∑ c, J x c

/-- Marginal of the second coordinate. -/
noncomputable def mC (J : X → C → ℝ) (c : C) : ℝ := ∑ x, J x c

/-- Joint entropy. -/
noncomputable def entJ (J : X → C → ℝ) : ℝ := ∑ c, ∑ x, negMulLog (J x c)

/-- Mutual information. -/
noncomputable def mi (J : X → C → ℝ) : ℝ := ent (mX J) + ent (mC J) - entJ J

/-- Conditional distribution of `x` given `c`. -/
noncomputable def cond (J : X → C → ℝ) (c : C) (x : X) : ℝ := J x c / mC J c

/-- Image of a distribution under a kernel. -/
noncomputable def img (q : X → ℝ) (k : X → Y → ℝ) (y : Y) : ℝ := ∑ x, q x * k x y

/-- Final state under closed-loop control. -/
noncomputable def closed (J : X → C → ℝ) (K : C → X → Y → ℝ) (y : Y) : ℝ :=
  ∑ c, ∑ x, J x c * K c x y

variable {J : X → C → ℝ} {K : C → X → Y → ℝ}

theorem mC_nonneg (hJ : ∀ x c, 0 ≤ J x c) (c : C) : 0 ≤ mC J c := sum_nonneg fun x _ => hJ x c

theorem J_zero (hJ : ∀ x c, 0 ≤ J x c) {c : C} (h : mC J c = 0) (x : X) : J x c = 0 :=
  (sum_eq_zero_iff_of_nonneg fun x _ => hJ x c).1 h x (mem_univ x)

theorem J_eq (hJ : ∀ x c, 0 ≤ J x c) (c : C) (x : X) : J x c = mC J c * cond J c x := by
  unfold cond
  rcases eq_or_ne (mC J c) 0 with h | h
  · rw [J_zero hJ h, h]; simp
  · field_simp

theorem cond_nonneg (hJ : ∀ x c, 0 ≤ J x c) (c : C) (x : X) : 0 ≤ cond J c x :=
  div_nonneg (hJ x c) (mC_nonneg hJ c)

theorem cond_sum {c : C} (h : mC J c ≠ 0) : ∑ x, cond J c x = 1 := by
  unfold cond; rw [← sum_div]; exact div_self h

/-- **Chain rule.** -/
theorem cond_chain (hJ : ∀ x c, 0 ≤ J x c) :
    entJ J = ent (mC J) + ∑ c, mC J c * ent (cond J c) := by
  rw [ent_eq, entJ, ← sum_add_distrib]
  refine sum_congr rfl fun c _ => ?_
  rcases eq_or_ne (mC J c) 0 with h | h
  · simp [J_zero hJ h, h]
  · rw [ent_eq, mul_sum]
    have : ∀ x, negMulLog (J x c) =
        cond J c x * negMulLog (mC J c) + mC J c * negMulLog (cond J c x) := by
      intro x
      conv_lhs => rw [J_eq hJ c x, negMulLog_mul]
    rw [sum_congr rfl fun x _ => this x, sum_add_distrib, ← sum_mul, cond_sum h, one_mul]

/-- **Entropy is concave.** -/
theorem ent_mix_ge {p : C → ℝ} (hp : ∀ c, 0 ≤ p c) (h1 : ∑ c, p c = 1) {Q : C → Y → ℝ}
    (hQ : ∀ c y, 0 ≤ Q c y) : ∑ c, p c * ent (Q c) ≤ ent fun y => ∑ c, p c * Q c y := by
  rw [ent_eq]
  have : ∑ c, p c * ent (Q c) = ∑ y, ∑ c, p c * negMulLog (Q c y) := by
    rw [sum_comm]; exact sum_congr rfl fun c _ => by rw [ent_eq, mul_sum]
  rw [this]
  refine sum_le_sum fun y _ => ?_
  simpa using concaveOn_negMulLog.le_map_sum (t := univ) (w := p) (p := fun c => Q c y)
    (fun c _ => hp c) h1 (fun c _ => hQ c y)

theorem mC_sum (h1 : ∑ x, ∑ c, J x c = 1) : ∑ c, mC J c = 1 := by
  unfold mC; rw [sum_comm]; exact h1

theorem closed_eq (hJ : ∀ x c, 0 ≤ J x c) :
    closed J K = fun y => ∑ c, mC J c * img (cond J c) (K c) y := by
  funext y
  refine sum_congr rfl fun c _ => ?_
  rw [img, mul_sum]
  exact sum_congr rfl fun x _ => by rw [← mul_assoc, ← J_eq hJ c x]

/-- **Touchette–Lloyd.** `D` bounds the entropy reduction of every pure control on every input. -/
theorem touchette_lloyd (hJ : ∀ x c, 0 ≤ J x c) (h1 : ∑ x, ∑ c, J x c = 1)
    (hK : ∀ c x y, 0 ≤ K c x y) {D : ℝ}
    (hD : ∀ c (q : X → ℝ), (∀ x, 0 ≤ q x) → ∑ x, q x = 1 → ent q - ent (img q (K c)) ≤ D) :
    ent (mX J) - ent (closed J K) ≤ D + mi J := by
  have hmix : ∑ c, mC J c * ent (img (cond J c) (K c)) ≤ ent (closed J K) := by
    rw [closed_eq hJ]
    exact ent_mix_ge (mC_nonneg hJ) (mC_sum h1) fun c y =>
      sum_nonneg fun x _ => mul_nonneg (cond_nonneg hJ c x) (hK c x y)
  have hstep : ∑ c, mC J c * ent (cond J c) - D ≤
      ∑ c, mC J c * ent (img (cond J c) (K c)) := by
    have : D = ∑ c, mC J c * D := by rw [← sum_mul, mC_sum h1, one_mul]
    rw [this, ← sum_sub_distrib]
    refine sum_le_sum fun c _ => ?_
    rcases eq_or_ne (mC J c) 0 with h | h
    · simp [h]
    · have := hD c (cond J c) (cond_nonneg hJ c) (cond_sum h)
      have hm := mC_nonneg hJ c
      nlinarith
  have := cond_chain hJ
  unfold mi
  linarith

/-! ### Supremum form -/

/-- All entropy reductions available to pure controls on any input distribution. -/
def openSet (K : C → X → Y → ℝ) : Set ℝ :=
  {t | ∃ c, ∃ q : X → ℝ, (∀ x, 0 ≤ q x) ∧ ∑ x, q x = 1 ∧ t = ent q - ent (img q (K c))}

/-- Largest open-loop entropy reduction. -/
noncomputable def openMax (K : C → X → Y → ℝ) : ℝ := sSup (openSet K)

theorem ent_nonneg {q : X → ℝ} (hq : ∀ x, 0 ≤ q x) (h1 : ∑ x, q x = 1) : 0 ≤ ent q := by
  rw [ent_eq]
  refine sum_nonneg fun x _ => negMulLog_nonneg (hq x) ?_
  rw [← h1]; exact single_le_sum (f := q) (fun x _ => hq x) (mem_univ x)

theorem img_nonneg {q : X → ℝ} (hq : ∀ x, 0 ≤ q x) {k : X → Y → ℝ} (hk : ∀ x y, 0 ≤ k x y)
    (y : Y) : 0 ≤ img q k y := sum_nonneg fun x _ => mul_nonneg (hq x) (hk x y)

theorem img_sum {q : X → ℝ} (h1 : ∑ x, q x = 1) {k : X → Y → ℝ} (hk : ∀ x, ∑ y, k x y = 1) :
    ∑ y, img q k y = 1 := by
  unfold img; rw [sum_comm]
  rw [← h1]; exact sum_congr rfl fun x _ => by rw [← mul_sum, hk, mul_one]

theorem openSet_bdd (hK : ∀ c x y, 0 ≤ K c x y) (hK1 : ∀ c x, ∑ y, K c x y = 1) :
    BddAbove (openSet K) := by
  refine ⟨log (Fintype.card X), ?_⟩
  rintro t ⟨c, q, hq, h1, rfl⟩
  have a := ent_le_log_card hq h1
  have b := ent_nonneg (img_nonneg hq (hK c)) (img_sum h1 (hK1 c))
  linarith

/-- **Touchette–Lloyd with the maximum over input distributions and pure controls.** -/
theorem touchette_lloyd_sup (hJ : ∀ x c, 0 ≤ J x c) (h1 : ∑ x, ∑ c, J x c = 1)
    (hK : ∀ c x y, 0 ≤ K c x y) (hK1 : ∀ c x, ∑ y, K c x y = 1) :
    ent (mX J) - ent (closed J K) ≤ openMax K + mi J :=
  touchette_lloyd hJ h1 hK fun c q hq hq1 =>
    le_csSup (openSet_bdd hK hK1) ⟨c, q, hq, hq1, rfl⟩

/-! ### Mutual information -/

theorem mX_eq_mix (hJ : ∀ x c, 0 ≤ J x c) : mX J = fun x => ∑ c, mC J c * cond J c x := by
  funext x; exact sum_congr rfl fun c _ => J_eq hJ c x

theorem mi_nonneg (hJ : ∀ x c, 0 ≤ J x c) (h1 : ∑ x, ∑ c, J x c = 1) : 0 ≤ mi J := by
  have h := ent_mix_ge (mC_nonneg hJ) (mC_sum h1) (Q := cond J) (cond_nonneg hJ)
  rw [← mX_eq_mix hJ] at h
  have := cond_chain hJ
  unfold mi; linarith

theorem ent_le_entJ (hJ : ∀ x c, 0 ≤ J x c) : ent (mX J) ≤ entJ J := by
  rw [ent_eq, entJ, sum_comm]
  refine sum_le_sum fun x _ => ?_
  have e : negMulLog (mX J x) = ∑ c, -(J x c * log (mX J x)) := by
    rw [sum_neg_distrib, ← sum_mul]; unfold negMulLog mX; ring
  rw [e]
  refine sum_le_sum fun c _ => ?_
  rcases (hJ x c).eq_or_lt with h | h
  · rw [← h]; simp
  · have hle : J x c ≤ mX J x :=
      single_le_sum (f := fun c => J x c) (fun c _ => hJ x c) (mem_univ c)
    have := log_le_log h hle
    unfold negMulLog; nlinarith

theorem mi_le_log_card (hJ : ∀ x c, 0 ≤ J x c) (h1 : ∑ x, ∑ c, J x c = 1) :
    mi J ≤ log (Fintype.card C) := by
  have a := ent_le_entJ hJ
  have b := ent_le_log_card (mC_nonneg hJ) (mC_sum h1)
  unfold mi; linarith

/-- A controller with `|C|` states adds at most `log |C|` to what open-loop control can do. -/
theorem reduction_le_messages (hJ : ∀ x c, 0 ≤ J x c) (h1 : ∑ x, ∑ c, J x c = 1)
    (hK : ∀ c x y, 0 ≤ K c x y) (hK1 : ∀ c x, ∑ y, K c x y = 1) :
    ent (mX J) - ent (closed J K) ≤ openMax K + log (Fintype.card C) :=
  (touchette_lloyd_sup hJ h1 hK hK1).trans (by linarith [mi_le_log_card hJ h1])

/-! ### Equality, and why the maximum over inputs is needed -/

/-- Perfect record of a fair bit. -/
noncomputable def Jbit (x c : Bool) : ℝ := if x = c then 1 / 2 else 0

/-- Controlled flip: `y = x xor c`. -/
noncomputable def Kbit (c x y : Bool) : ℝ := if y = xor x c then 1 else 0

/-- **Equality is attained.** Open-loop control cannot reduce entropy at all (each control is a
permutation), feedback removes the whole bit, and `I(X;C) = log 2`. -/
theorem cnot_tight :
    (∀ c (q : Bool → ℝ), ent q - ent (img q (Kbit c)) = 0) ∧ mi Jbit = log 2 ∧
      ent (mX Jbit) - ent (closed Jbit Kbit) = log 2 := by
  refine ⟨fun c q => ?_, ?_, ?_⟩
  · cases c <;> simp [ent, img, Kbit] <;> ring
  · simp [mi, ent, mX, mC, entJ, Jbit, negMulLog]
  · have a : mX Jbit = fun _ => (2⁻¹ : ℝ) := by funext x; cases x <;> simp [mX, Jbit]
    have b : closed Jbit Kbit = fun y => if y = false then 1 else 0 := by
      funext y; cases y <;> simp [closed, Jbit, Kbit] <;> norm_num
    rw [a, b]
    simp [ent]

/-- Four equally likely states; the controller knows which half. -/
noncomputable def J4 (x : Fin 4) (c : Bool) : ℝ :=
  if (c = true ↔ (x : ℕ) < 2) then 1 / 4 else 0

/-- `c = true` merges `0,1`; `c = false` merges `2,3` (into state 0). -/
def step4 : Bool → Fin 4 → Fin 4
  | true => ![0, 0, 2, 3]
  | false => ![1, 2, 0, 0]

noncomputable def K4 (c : Bool) (x y : Fin 4) : ℝ := if y = step4 c x then 1 else 0

theorem log_four : log (4 : ℝ) = 2 * log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; push_cast; ring

/-- **The bound fails if the open-loop term is taken only at the current state.** -/
theorem same_state_fails :
    (∀ c, ent (mX J4) - ent (img (mX J4) (K4 c)) = log 2 / 2) ∧ mi J4 = log 2 ∧
      ent (mX J4) - ent (closed J4 K4) = 2 * log 2 ∧
      log 2 / 2 + mi J4 < ent (mX J4) - ent (closed J4 K4) := by
  have hm : mX J4 = fun _ => (4⁻¹ : ℝ) := by
    funext x; fin_cases x <;> simp [mX, J4]
  have hc : mC J4 = fun _ => (2⁻¹ : ℝ) := by
    funext c; cases c <;> simp [mC, J4, Fin.sum_univ_four] <;> norm_num
  have hH : ent (mX J4) = 2 * log 2 := by
    rw [hm]; simp only [ent, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, log_inv, log_four]
    push_cast; ring
  have hI : mi J4 = log 2 := by
    unfold mi; rw [hH, hc]
    simp [ent, entJ, J4, negMulLog, Fin.sum_univ_four]
    rw [log_four]; ring
  have hcl : closed J4 K4 = fun y => if y = 0 then 1 else 0 := by
    funext y; fin_cases y <;>
      simp [closed, J4, K4, step4, Fin.sum_univ_four] <;> norm_num
  have hC : ent (mX J4) - ent (closed J4 K4) = 2 * log 2 := by
    rw [hH, hcl]; simp [ent]
  have hO : ∀ c, ent (mX J4) - ent (img (mX J4) (K4 c)) = log 2 / 2 := by
    intro c
    have hi : ∀ c, ent (img (mX J4) (K4 c)) = 3 / 2 * log 2 := by
      intro c; rw [hm]
      cases c
      · have : img (fun _ => (4⁻¹ : ℝ)) (K4 false) = ![2⁻¹, 4⁻¹, 4⁻¹, 0] := by
          funext y; fin_cases y <;> simp [img, K4, step4, Fin.sum_univ_four] <;> norm_num
        rw [this]; simp [ent, Fin.sum_univ_four]; rw [log_four]; ring
      · have : img (fun _ => (4⁻¹ : ℝ)) (K4 true) = ![2⁻¹, 0, 4⁻¹, 4⁻¹] := by
          funext y; fin_cases y <;> simp [img, K4, step4, Fin.sum_univ_four] <;> norm_num
        rw [this]; simp [ent, Fin.sum_univ_four]; rw [log_four]; ring
    rw [hH, hi]; ring
  refine ⟨hO, hI, hC, ?_⟩
  rw [hI, hC]; have := log_pos (by norm_num : (1 : ℝ) < 2); linarith

end FiveOrgans.ControlEntropy
