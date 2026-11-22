import FiveOrgans.CrossScaleTest

/-!
# A horizon-free bound for the φ test

`sv_approx_lump` / `CrossScaleTest.data_test` bound the micro–macro survival gap by `n η`, which
says nothing once `n ≥ 1/η`. This module replaces the linear bound by one that does not grow with
`n` whenever the macro model has a minimum per-step exit probability `q > 0` on the viable set.

* `sv_gap_rec` — **error recursion:** if the micro stay-probability on `φ⁻¹ K` is `≤ a` and macro
  survival at step `n` is `≤ b n`, the gap is `≤ B n` with `B 0 = 0`, `B (n+1) = a B n + η b n`.
  (`a = 1`, `b = 1` recovers `n η`.)
* `B_decay` — closed form when `a ≤ 1` and `b n = C ρⁿ`: `B n ≤ η C (1 − ρⁿ)/(1 − ρ) ≤ η C/(1 − ρ)`.
* `sv_gap_uniform` — **horizon-free transfer:** if every macro state in `K` exits with probability
  `≥ q > 0` per step, then `|micro survival − macro survival| ≤ η / q` **for every `n`**.
* `data_test_uniform` — the same with the macro kernel `Qhat` read off the data: the gap is
  `≤ (η + δ)/q`, where `η` (within-block spread) and `q` (exit probability of `Qhat`) are both
  computed from logs, and `δ` is the sampling assumption of `CrossScaleTest`.
* `no_uniform_without_exit` — **sharpness:** without a macro exit probability no horizon-free bound
  exists. A chain with defect `≤ 2η` against a macro model that never dies has survival gap
  `1 − (1 − η)ⁿ`, which exceeds every `c < 1` eventually.

Reading: with killing, the error accumulated `k` steps ago is discounted by the probability of
still being alive, so it sums geometrically. Without killing, errors genuinely add up.
-/

namespace FiveOrgans.CrossScaleContract
open Finset Classical FiveOrgans.CrossScaleMarkov FiveOrgans.CrossScaleTest

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The error recursion `B 0 = 0`, `B (n+1) = a B n + η b n`. -/
def B (a η : ℝ) (b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => a * B a η b n + η * b n

theorem B_nonneg {a η : ℝ} {b : ℕ → ℝ} (ha : 0 ≤ a) (hη : 0 ≤ η) (hb : ∀ n, 0 ≤ b n) (n : ℕ) :
    0 ≤ B a η b n := by
  induction n with
  | zero => simp [B]
  | succ n ih => simp only [B]; exact add_nonneg (mul_nonneg ha ih) (mul_nonneg hη (hb n))

/-- **Error recursion** for the micro–macro survival gap. -/
theorem sv_gap_rec {φ : X → Y} {P : X → X → ℝ} {Q : Y → Y → ℝ}
    (hP : ∀ x x', 0 ≤ P x x') (hQ : ∀ y y', 0 ≤ Q y y') {η a : ℝ} {b : ℕ → ℝ}
    (hη : ∀ x, defect φ P Q x ≤ η) (K : Set Y) (ha : 0 ≤ a)
    (hstay : ∀ x ∈ φ ⁻¹' K, stayP P (φ ⁻¹' K) x ≤ a)
    (hb : ∀ n y, sv Q K n y ≤ b n) (hb0 : ∀ n, 0 ≤ b n) (n : ℕ) (x : X) :
    |sv P (φ ⁻¹' K) n x - sv Q K n (φ x)| ≤ B a η b n := by
  unfold defect blk at hη
  have hη0 : 0 ≤ η := (sum_nonneg fun _ _ => abs_nonneg _).trans (hη x)
  induction n generalizing x with
  | zero => simp [sv, Set.mem_preimage, B]
  | succ n ih =>
    simp only [sv, Set.mem_preimage]
    split_ifs with hx
    · set g := sv Q K n
      have hsplit : ∑ x', P x x' * sv P (φ ⁻¹' K) n x' - ∑ y', Q (φ x) y' * g y'
          = ∑ x', P x x' * (sv P (φ ⁻¹' K) n x' - g (φ x'))
            + ∑ y', ((∑ x' ∈ univ.filter (fun x' => φ x' = y'), P x x') - Q (φ x) y') * g y' := by
        have e := fiber_sum φ P g x
        simp_rw [mul_sub, sub_mul, sum_sub_distrib]
        rw [← e]; ring
      rw [hsplit]
      have hBn := B_nonneg ha hη0 hb0 n
      have hpt : ∀ x', |sv P (φ ⁻¹' K) n x' - g (φ x')|
          ≤ B a η b n * (if x' ∈ φ ⁻¹' K then 1 else 0) := by
        intro x'
        split_ifs with h'
        · simpa using ih x'
        · rw [sv_out n h', show g (φ x') = 0 from sv_out n (show φ x' ∉ K from h')]
          simp
      have h1 : |∑ x', P x x' * (sv P (φ ⁻¹' K) n x' - g (φ x'))| ≤ a * B a η b n :=
        calc _ ≤ ∑ x', |P x x' * (sv P (φ ⁻¹' K) n x' - g (φ x'))| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ x', P x x' * (B a η b n * (if x' ∈ φ ⁻¹' K then 1 else 0)) :=
              sum_le_sum fun x' _ => by
                rw [abs_mul, abs_of_nonneg (hP x x')]
                exact mul_le_mul_of_nonneg_left (hpt x') (hP x x')
          _ = B a η b n * stayP P (φ ⁻¹' K) x := by
              unfold stayP; rw [mul_sum]; exact sum_congr rfl fun x' _ => by ring
          _ ≤ B a η b n * a := mul_le_mul_of_nonneg_left (hstay x hx) hBn
          _ = a * B a η b n := mul_comm _ _
      have h2 : |∑ y', ((∑ x' ∈ univ.filter (fun x' => φ x' = y'), P x x') - Q (φ x) y') * g y'|
          ≤ η * b n :=
        calc _ ≤ ∑ y', |((∑ x' ∈ univ.filter (fun x' => φ x' = y'), P x x') - Q (φ x) y') * g y'| :=
              abs_sum_le_sum_abs _ _
          _ ≤ ∑ y', |(∑ x' ∈ univ.filter (fun x' => φ x' = y'), P x x') - Q (φ x) y'| * b n :=
              sum_le_sum fun y' _ => by
                rw [abs_mul, abs_of_nonneg (sv_nonneg hQ K n y')]
                exact mul_le_mul_of_nonneg_left (hb n y') (abs_nonneg _)
          _ = (∑ y', |(∑ x' ∈ univ.filter (fun x' => φ x' = y'), P x x') - Q (φ x) y'|) * b n :=
              (sum_mul _ _ _).symm
          _ ≤ η * b n := mul_le_mul_of_nonneg_right (hη x) (hb0 n)
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ a * B a η b n + η * b n := add_le_add h1 h2
        _ = B a η b (n + 1) := rfl
    · rw [sub_self, abs_zero]; exact B_nonneg ha hη0 hb0 _

/-- Closed form under geometric decay of macro survival. -/
theorem B_decay {a η C ρ : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1) (hη : 0 ≤ η) (hC : 0 ≤ C)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (n : ℕ) :
    B a η (fun k => C * ρ ^ k) n ≤ η * C * (1 - ρ ^ n) / (1 - ρ) := by
  have h1ρ : 0 < 1 - ρ := by linarith
  induction n with
  | zero => simp [B]
  | succ n ih =>
    simp only [B]
    have hB := B_nonneg ha0 hη (fun k => mul_nonneg hC (pow_nonneg hρ0 k)) n
    have hab : a * B a η (fun k => C * ρ ^ k) n ≤ B a η (fun k => C * ρ ^ k) n :=
      mul_le_of_le_one_left hB ha
    have he : η * C * (1 - ρ ^ n) / (1 - ρ) + η * (C * ρ ^ n)
        = η * C * (1 - ρ ^ (n + 1)) / (1 - ρ) := by
      field_simp
      ring
    linarith

theorem B_decay_le {a η C ρ : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1) (hη : 0 ≤ η) (hC : 0 ≤ C)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (n : ℕ) :
    B a η (fun k => C * ρ ^ k) n ≤ η * C / (1 - ρ) := by
  have h1ρ : 0 < 1 - ρ := by linarith
  refine (B_decay ha0 ha hη hC hρ0 hρ n).trans ?_
  apply div_le_div_of_nonneg_right _ h1ρ.le
  have := pow_nonneg hρ0 n
  nlinarith [mul_nonneg hη hC]

theorem stayP_le_one {P : X → X → ℝ} (hP : ∀ x x', 0 ≤ P x x') (hrow : ∀ x, ∑ x', P x x' ≤ 1)
    (K : Set X) (x : X) : stayP P K x ≤ 1 := by
  unfold stayP
  calc ∑ x', P x x' * (if x' ∈ K then 1 else 0) ≤ ∑ x', P x x' :=
        sum_le_sum fun x' _ => by
          split_ifs
          · simp
          · simpa using hP x x'
    _ ≤ 1 := hrow x

/-- **Horizon-free transfer.** If every macro state in `K` exits with probability `≥ q > 0` per
step, the survival gap is at most `η / q` at every horizon. -/
theorem sv_gap_uniform {φ : X → Y} {P : X → X → ℝ} {Q : Y → Y → ℝ}
    (hP : ∀ x x', 0 ≤ P x x') (hrow : ∀ x, ∑ x', P x x' ≤ 1)
    (hQ : ∀ y y', 0 ≤ Q y y') (hQrow : ∀ y, ∑ y', Q y y' ≤ 1) {η q : ℝ}
    (hη : ∀ x, defect φ P Q x ≤ η) {K : Set Y} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hexit : ∀ y ∈ K, stayP Q K y ≤ 1 - q) (n : ℕ) (x : X) :
    |sv P (φ ⁻¹' K) n x - sv Q K n (φ x)| ≤ η / q := by
  have hη0 : 0 ≤ η := (sum_nonneg fun _ _ => abs_nonneg _).trans (hη x)
  have hr := sv_gap_rec (a := 1) (b := fun k => 1 * (1 - q) ^ k) hP hQ hη K zero_le_one
    (fun x _ => stayP_le_one hP hrow _ x)
    (fun n y => by simpa using markov_hazard_upper hQ hQrow hq1 hexit n y)
    (fun k => by have : 0 ≤ 1 - q := by linarith
                 positivity) n x
  have hd := B_decay_le (a := 1) (C := 1) (ρ := 1 - q) zero_le_one le_rfl hη0 zero_le_one
    (by linarith) (by linarith) n
  have : η * 1 / (1 - (1 - q)) = η / q := by ring_nf
  linarith

/-- **Horizon-free data test.** `Qhat` and `η` (within-block spread) come from the logs, `q` is
the minimum exit probability of `Qhat` on `K` (also from the logs), `δ` bounds the row errors
(sampling assumption). Then the true micro survival is within `(η + δ)/q` of `Qhat` survival at
every horizon. -/
theorem data_test_uniform {φ : X → Y} {P Ph : X → X → ℝ} (r : Y → X)
    (hP : ∀ x x', 0 ≤ P x x') (hrow : ∀ x, ∑ x', P x x' ≤ 1)
    (hPh : ∀ x x', 0 ≤ Ph x x') (hPhrow : ∀ x, ∑ x', Ph x x' ≤ 1) {δ η q : ℝ}
    (hδ : ∀ x, rowErr P Ph x ≤ δ) (hη : ∀ x, spread φ Ph r x ≤ η)
    {K : Set Y} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hexit : ∀ y ∈ K, stayP (Qhat φ Ph r) K y ≤ 1 - q) (n : ℕ) (x : X) :
    |sv P (φ ⁻¹' K) n x - sv (Qhat φ Ph r) K n (φ x)| ≤ (η + δ) / q :=
  sv_gap_uniform hP hrow (fun y y' => blk_nonneg φ hPh (r y) y')
    (fun y => (blk_sum φ Ph (r y)).trans_le (hPhrow (r y)))
    (fun x => by
      have h1 := defect_transfer φ P Ph (Qhat φ Ph r) x
      have h2 := hη x
      have h3 := hδ x
      rw [spread_eq_defect] at h2
      show defect φ P (Qhat φ Ph r) x ≤ η + δ
      linarith) hq0 hq1 hexit n x

/-! ### Sharpness: no horizon-free bound without a macro exit probability -/

/-- Micro: the viable state `true` leaks to the absorbing dead state `false` with probability `η`. -/
noncomputable def Pl (η : ℝ) : Bool → Bool → ℝ := fun x x' =>
  if x then (if x' then 1 - η else η) else (if x' then 0 else 1)

/-- Macro: nothing ever moves (no exit from `true`). -/
noncomputable def Qs : Bool → Bool → ℝ := fun x x' => if x = x' then 1 else 0

theorem Pl_sv (η : ℝ) (n : ℕ) : sv (Pl η) {true} n true = (1 - η) ^ n := by
  induction n with
  | zero => simp [sv]
  | succ n ih =>
    have h0 : sv (Pl η) {true} n false = 0 := sv_out n (by simp)
    simp [sv, Pl, ih, h0, pow_succ, mul_comm]

theorem Qs_sv (n : ℕ) : sv Qs {true} n true = 1 := by
  induction n with
  | zero => simp [sv]
  | succ n ih => simp [sv, Qs, ih]

theorem Pl_defect {η : ℝ} (h0 : 0 ≤ η) (x : Bool) :
    defect id (Pl η) Qs x ≤ 2 * η := by
  cases x <;> simp [defect, blk, Pl, Qs, Finset.filter_eq', abs_of_nonneg h0] <;> linarith

/-- **Sharpness.** For any leak `0 < η < 1` the chain `Pl η` is within `2η` of a macro model with
no exit, yet the survival gap exceeds every `c < 1` at some horizon. So the exit hypothesis of
`sv_gap_uniform` cannot be dropped: without it the linear-in-`n` growth is real. -/
theorem no_uniform_without_exit {η : ℝ} (h0 : 0 < η) (h1 : η < 1) {c : ℝ} (hc : c < 1) :
    (∀ x, defect id (Pl η) Qs x ≤ 2 * η) ∧
    ∃ n, c < |sv (Pl η) (id ⁻¹' {true}) n true - sv Qs {true} n (id true)| := by
  refine ⟨Pl_defect h0.le, ?_⟩
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < 1 - c by linarith) (show 1 - η < 1 by linarith)
  refine ⟨n, ?_⟩
  rw [Set.preimage_id, Pl_sv, id, Qs_sv, abs_sub_comm, abs_of_nonneg (by
    have := pow_le_one₀ (show 0 ≤ 1 - η by linarith) (show 1 - η ≤ 1 by linarith) (n := n)
    linarith)]
  linarith

end FiveOrgans.CrossScaleContract
