import FiveOrgans.SensingRate
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Knowing the start does not lower the sensing threshold

`SensingRate.forever_iff` assumes the start is unknown in the whole safe interval. Here the start is
known to both encoder and controller. With disturbance `d > 0` the threshold is **the same**
(`known_start_iff`): the set of states compatible with the messages loses at most a factor `M` in
length per message and gains `2 d` per step, so below the threshold some message history leaves an
uncertainty set longer than the safe interval.

Scope: worst case, scalar, linear, unlimited actuation, no delay. With `d = 0` a known start needs no
messages, so `d > 0` is necessary.
-/

namespace FiveOrgans.SensingRate
open MeasureTheory Set
open scoped Pointwise

variable {M : ℕ} {a r d : ℝ}

/-- Points within `d` of `A`. -/
def fat (d : ℝ) (A : Set ℝ) : Set ℝ := {y | ∃ x ∈ A, |y - x| ≤ d}

/-- A bounded disturbance adds at least `2 d` of length. -/
theorem vol_fat {A : Set ℝ} (hne : A.Nonempty) (hb : A ⊆ Icc (-r) r) (hd : 0 < d) :
    volume A + ENNReal.ofReal (2 * d) ≤ volume (fat d A) := by
  have ha : BddAbove A := ⟨r, fun x hx => (hb hx).2⟩
  have hl : BddBelow A := ⟨-r, fun x hx => (hb hx).1⟩
  have hAs : ∀ x ∈ A, x ≤ sSup A := fun x hx => le_csSup ha hx
  have hAi : ∀ x ∈ A, sInf A ≤ x := fun x hx => csInf_le hl hx
  have his : sInf A ≤ sSup A := by obtain ⟨x, hx⟩ := hne; exact (hAi x hx).trans (hAs x hx)
  have h1 : Ioo (sSup A) (sSup A + d) ⊆ fat d A := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := exists_lt_of_lt_csSup hne (show y - d < sSup A by linarith [hy.2])
    exact ⟨x, hx, abs_le.2 ⟨by linarith [hAs x hx, hy.1], by linarith⟩⟩
  have h2 : Ioo (sInf A - d) (sInf A) ⊆ fat d A := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := exists_lt_of_csInf_lt hne (show sInf A < y + d by linarith [hy.1])
    exact ⟨x, hx, abs_le.2 ⟨by linarith, by linarith [hAi x hx, hy.2]⟩⟩
  have h0 : A ⊆ fat d A := fun x hx => ⟨x, hx, by simpa using hd.le⟩
  have d1 : Disjoint A (Ioo (sSup A) (sSup A + d)) :=
    Set.disjoint_left.2 fun x hx hy => absurd (hAs x hx) (not_le.2 hy.1)
  have d2 : Disjoint (A ∪ Ioo (sSup A) (sSup A + d)) (Ioo (sInf A - d) (sInf A)) := by
    refine Set.disjoint_left.2 fun x hx hy => ?_
    rcases hx with hx | hx
    · exact absurd (hAi x hx) (not_le.2 hy.2)
    · linarith [hx.1, hy.2]
  calc volume A + ENNReal.ofReal (2 * d)
      = volume A + volume (Ioo (sSup A) (sSup A + d)) + volume (Ioo (sInf A - d) (sInf A)) := by
        rw [Real.volume_Ioo, Real.volume_Ioo, add_assoc, ← ENNReal.ofReal_add (by linarith)
          (by linarith)]
        congr 2; ring
    _ = volume (A ∪ Ioo (sSup A) (sSup A + d) ∪ Ioo (sInf A - d) (sInf A)) := by
        rw [measure_union d2 measurableSet_Ioo, measure_union d1 measurableSet_Ioo]
    _ ≤ volume (fat d A) := measure_mono (union_subset (union_subset h0 h1) h2)

/-- States compatible with message history `ms` at time `n`. -/
def reach (a d : ℝ) (S : Strat M) (x₀ : ℝ) (n : ℕ) (ms : List (Fin M)) : Set ℝ :=
  {x | ∃ w : ℕ → ℝ, (∀ k, |w k| ≤ d) ∧ (hist a S x₀ w n).2 = ms ∧ st a S x₀ w n = x}

/-- The past does not depend on future disturbances. -/
theorem hist_congr {S : Strat M} {x₀ : ℝ} {w w' : ℕ → ℝ} :
    ∀ n, (∀ k < n, w k = w' k) → hist a S x₀ w n = hist a S x₀ w' n
  | 0, _ => rfl
  | n + 1, h => by
    have ih := hist_congr (S := S) (x₀ := x₀) n fun k hk => h k (by omega)
    simp only [hist, ih, h n (by omega)]

/-- Every point of the image of a reachable set is reachable one step later under some message. -/
theorem reach_step {S : Strat M} {x₀ : ℝ} {n : ℕ} {ms : List (Fin M)} :
    fat d (S.act ms +ᵥ (a • reach a d S x₀ n ms)) ⊆
      ⋃ m : Fin M, reach a d S x₀ (n + 1) (m :: ms) := by
  rintro y ⟨z, hz, hy⟩
  obtain ⟨v, hv, rfl⟩ := Set.mem_vadd_set.1 hz
  obtain ⟨x, ⟨w, hw, hms, hx⟩, rfl⟩ := Set.mem_smul_set.1 hv
  simp only [vadd_eq_add, smul_eq_mul] at hy
  set w' := Function.update w n (y - (S.act ms + a * x)) with hw'
  have hc : hist a S x₀ w' n = hist a S x₀ w n :=
    hist_congr n fun k hk => Function.update_of_ne (by omega) _ _
  have hs : st a S x₀ w' (n + 1) = y := by
    show a * (hist a S x₀ w' n).1.headD 0 + S.act (hist a S x₀ w' n).2 + w' n = y
    rw [hc, hms]
    have : (hist a S x₀ w n).1.headD 0 = x := hx
    rw [this, hw', Function.update_self]; ring
  refine mem_iUnion.2 ⟨S.enc ((hist a S x₀ w' (n + 1)).1), w', fun k => ?_, ?_, hs⟩
  · rcases eq_or_ne k n with rfl | hk
    · rw [hw', Function.update_self]; exact hy
    · rw [hw', Function.update_of_ne hk]; exact hw k
  · show S.enc _ :: (hist a S x₀ w' n).2 = _
    rw [hc, hms]; simp only [hist]
    rw [hc, hms]

/-- Survives for ever from the known start `x₀`. -/
def ViableFrom (a r d : ℝ) (S : Strat M) (x₀ : ℝ) : Prop :=
  ∀ w : ℕ → ℝ, (∀ n, |w n| ≤ d) → ∀ n, |st a S x₀ w n| ≤ r

/-- Length of the uncertainty set after `n` steps is at least `v n`. -/
theorem grow (hM : 0 < M) (hd : 0 < d) {S : Strat M} {x₀ : ℝ}
    (hS : ViableFrom a r d S x₀) {n : ℕ} {ms : List (Fin M)} {v : ℝ} (hv : 0 ≤ v)
    (hne : (reach a d S x₀ n ms).Nonempty)
    (h : ENNReal.ofReal v ≤ volume (reach a d S x₀ n ms)) :
    |a| * v + 2 * d ≤ 2 * r ∧ ∃ m, (reach a d S x₀ (n + 1) (m :: ms)).Nonempty ∧
      ENNReal.ofReal ((|a| * v + 2 * d) / M) ≤ volume (reach a d S x₀ (n + 1) (m :: ms)) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hr : 0 ≤ r := by
    obtain ⟨x, w, hw, -, -⟩ := hne
    exact (abs_nonneg _).trans (hS w hw 0)
  have hR : ∀ n ms, reach a d S x₀ n ms ⊆ Icc (-r) r := by
    rintro n ms x ⟨w, hw, -, rfl⟩
    exact abs_le.1 (hS w hw n)
  set C := S.act ms +ᵥ (a • reach a d S x₀ n ms) with hC
  have hCv : volume C = ENNReal.ofReal |a| * volume (reach a d S x₀ n ms) := by
    rw [hC, measure_vadd, Measure.addHaar_smul]; simp
  have hCf : fat d C ⊆ Icc (-r) r := by
    refine reach_step.trans (iUnion_subset fun m => hR _ _)
  have hCb : C ⊆ Icc (-r) r := fun x hx => hCf ⟨x, hx, by simpa using hd.le⟩
  have hCne : C.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨S.act ms +ᵥ (a • x), Set.vadd_mem_vadd_set (Set.smul_mem_smul_set hx)⟩
  have hF : ENNReal.ofReal (|a| * v + 2 * d) ≤ volume (fat d C) := by
    refine le_trans ?_ (vol_fat hCne hCb hd)
    rw [hCv, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (abs_nonneg a)]
    gcongr
  refine ⟨?_, ?_⟩
  · have h2 := hF.trans (measure_mono hCf)
    rw [Real.volume_Icc, ENNReal.ofReal_le_ofReal_iff (by linarith)] at h2
    linarith
  · by_contra hcon
    push Not at hcon
    have hlt : ∀ m, volume (reach a d S x₀ (n + 1) (m :: ms)) <
        ENNReal.ofReal ((|a| * v + 2 * d) / M) := by
      intro m
      rcases (reach a d S x₀ (n + 1) (m :: ms)).eq_empty_or_nonempty with he | hn
      · rw [he, measure_empty]
        exact ENNReal.ofReal_pos.2 (div_pos (by positivity) hM')
      · exact hcon m hn
    have hsum : volume (fat d C) ≤ ∑ m, volume (reach a d S x₀ (n + 1) (m :: ms)) :=
      (measure_mono reach_step).trans (measure_iUnion_fintype_le _ _)
    have : ∑ m : Fin M, volume (reach a d S x₀ (n + 1) (m :: ms)) <
        ∑ _m : Fin M, ENNReal.ofReal ((|a| * v + 2 * d) / M) := by
      have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
      exact ENNReal.sum_lt_sum_of_nonempty Finset.univ_nonempty fun m _ => hlt m
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hM'.le, mul_div_cancel₀ _ hM'.ne'] at this
    exact absurd (hF.trans hsum) (not_le.2 this)

/-- **Known start, same threshold.** -/
theorem known_start_iff (hM : 0 < M) (hr : 0 < r) (hd : 0 < d) {x₀ : ℝ} (hx₀ : |x₀| ≤ r) :
    (∃ S : Strat M, ViableFrom a r d S x₀) ↔ |a| * r + M * d ≤ M * r := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  constructor
  · rintro ⟨S, hS⟩
    by_contra hcon
    push Not at hcon
    set ε := min (2 * d / M) (2 * (|a| * r + M * d - M * r) / (M * M)) with hε
    have hε0 : 0 < ε := lt_min (by positivity) (div_pos (by linarith) (by positivity))
    have key : ∀ n : ℕ, ∃ ms v, 0 ≤ v ∧ v * M ≤ 2 * r ∧ n * ε ≤ v ∧ (reach a d S x₀ n ms).Nonempty ∧
        ENNReal.ofReal v ≤ volume (reach a d S x₀ n ms) := by
      intro n
      induction n with
      | zero =>
        exact ⟨_, 0, le_rfl, by linarith, by simp, ⟨x₀, fun _ => 0, fun _ => by simpa using hd.le, rfl, rfl⟩,
          by simp⟩
      | succ n ih =>
        obtain ⟨ms, v, hv, hvM, hn, hne, h⟩ := ih
        obtain ⟨hle, m, hne', h'⟩ := grow hM hd hS hv hne h
        refine ⟨m :: ms, _, by positivity, ?_, ?_, hne', h'⟩
        · rw [div_mul_cancel₀ _ hM'.ne']; exact hle
        have hstep : v + ε ≤ (|a| * v + 2 * d) / M := by
          rcases le_total (M : ℝ) |a| with hc | hc
          · have : ε ≤ 2 * d / M := min_le_left _ _
            rw [le_div_iff₀ hM'] at this ⊢; nlinarith
          · have h3 : ε ≤ 2 * (|a| * r + M * d - M * r) / (M * M) := min_le_right _ _
            rw [le_div_iff₀ (by positivity)] at h3
            rw [le_div_iff₀ hM']
            have h4 : (M - |a|) * (v * M) ≤ (M - |a|) * (2 * r) :=
              mul_le_mul_of_nonneg_left hvM (by linarith)
            have h5 : M * ((v + ε) * M) ≤ M * (|a| * v + 2 * d) := by nlinarith
            exact le_of_mul_le_mul_left h5 hM'
        push_cast; linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * r / M / ε)
    obtain ⟨ms, v, hv, hvM, hnv, -, -⟩ := key n
    rw [div_lt_iff₀ hε0] at hn
    have : v ≤ 2 * r / M := by rw [le_div_iff₀ hM']; exact hvM
    linarith
  · intro h
    obtain ⟨S, hS⟩ := (forever_iff hM hr hd.le).2 h
    exact ⟨S, fun w hw n => hS x₀ hx₀ w hw n⟩

end FiveOrgans.SensingRate
