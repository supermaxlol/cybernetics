import FiveOrgans.ViabilityStochastic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-!
# Stochastic cross-scale map: lumpability is the exact analogue of `Implements`

Micro system: a Markov chain on a finite state set `X` with kernel `P x x'`. Macro model: a chain
on `Y` with kernel `Q`. A map `φ : X → Y` is **lumpable** (Kemeny–Snell) onto `Q` if, from
every micro state `x`, the probability of jumping into the block `φ⁻¹{y'}` is `Q (φ x) y'`
(it depends on `x` only through `φ x`).

`sv P K n x` is the probability of staying in `K` for `n` steps from `x` (the state is checked
at steps `0 … n`). This is the state-level origin of the hazards in `ViabilityStochastic`.

* `lump_sum` — lumpability lets any function of the macro state be averaged at the macro level.
* `sv_lump` — **if φ is lumpable, micro survival in `φ⁻¹ K` equals macro survival in `K`,
  exactly, at every horizon.** `ablation_lump`: with lumpability under each intervention
  kernel, every ablation verdict transfers exactly (stochastic `CrossScale.ablation_kills_iff`).
* `survival_factors` — consequence: under lumpability, micro states with the same image have
  the same survival probability.
* `no_chain_of_split` — so if two micro states with the same image differ in survival, **no**
  macro chain on `Y` reproduces micro survival through φ.
* `split_instance` — a concrete 3-state chain where this happens: φ matches the viable/dead
  labelling, yet no macro kernel works.
* `lump_instance` — non-vacuity: a hidden coin on `Bool × Bool` lumps onto `Bool` by `fst`.

The identity in `sv_lump` is algebraic. It needs neither nonnegative entries nor rows summing to
1. Scope: finite, time-homogeneous chains.

State-dependent hazards and approximate lumpability:
* `markov_hazard_lower` / `markov_hazard_upper` — if the one-step exit probability from every
  state in `K` lies in `[q, h]`, survival lies in `[(1-h)^n, (1-q)^n]`. So the hazard results of
  `ViabilityStochastic` hold for state-dependent hazards via their worst and best states.
* `sv_approx_lump` — **approximate lumpability:** block-transition error `≤ η` (ℓ¹, per state)
  gives a survival gap `≤ n η`. This derives the hazard-level mismatch of `CrossScaleHazard`
  from a state-level stochastic φ. Whether a real organism has a lumpable coarse-graining onto
the five-organ model is EMP?.
-/

namespace FiveOrgans.CrossScaleMarkov
open Finset Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Probability of staying in `K` for `n` steps from `x`. -/
noncomputable def sv (P : X → X → ℝ) (K : Set X) : ℕ → X → ℝ
  | 0, x => if x ∈ K then 1 else 0
  | n + 1, x => if x ∈ K then ∑ x', P x x' * sv P K n x' else 0

/-- Kemeny–Snell lumpability of `P` onto `Q` through `φ`. -/
def Lumpable (φ : X → Y) (P : X → X → ℝ) (Q : Y → Y → ℝ) : Prop :=
  ∀ x y', ∑ x' ∈ univ.filter (fun x' => φ x' = y'), P x x' = Q (φ x) y'

theorem lump_sum {φ : X → Y} {P : X → X → ℝ} {Q : Y → Y → ℝ} (h : Lumpable φ P Q)
    (g : Y → ℝ) (x : X) : ∑ x', P x x' * g (φ x') = ∑ y', Q (φ x) y' * g y' := by
  rw [← Finset.sum_fiberwise univ φ (fun x' => P x x' * g (φ x'))]
  refine sum_congr rfl fun y' _ => ?_
  rw [← h x y', sum_mul]
  refine sum_congr rfl fun x' hx' => ?_
  rw [(mem_filter.1 hx').2]

/-- **Exact survival transfer under lumpability.** -/
theorem sv_lump {φ : X → Y} {P : X → X → ℝ} {Q : Y → Y → ℝ} (h : Lumpable φ P Q) (K : Set Y)
    (n : ℕ) (x : X) : sv P (φ ⁻¹' K) n x = sv Q K n (φ x) := by
  induction n generalizing x with
  | zero => simp [sv, Set.mem_preimage]
  | succ n ih =>
    simp only [sv, Set.mem_preimage]
    split_ifs
    · rw [show (∑ x', P x x' * sv P (φ ⁻¹' K) n x') = ∑ x', P x x' * sv Q K n (φ x') from
        sum_congr rfl fun x' _ => by rw [ih]]
      exact lump_sum h _ x
    · rfl

/-- **Ablations transfer exactly** when φ is lumpable under every intervention kernel. -/
theorem ablation_lump {I : Type*} {φ : X → Y} {P : I → X → X → ℝ} {Q : I → Y → Y → ℝ}
    (h : ∀ i, Lumpable φ (P i) (Q i)) (K : Set Y) (i : I) (n : ℕ) (x : X) :
    sv (P i) (φ ⁻¹' K) n x = sv (Q i) K n (φ x) :=
  sv_lump (h i) K n x

/-- Under lumpability, survival depends on the micro state only through its image. -/
theorem survival_factors {φ : X → Y} {P : X → X → ℝ} {Q : Y → Y → ℝ} (h : Lumpable φ P Q)
    (K : Set Y) (n : ℕ) {x₁ x₂ : X} (hφ : φ x₁ = φ x₂) :
    sv P (φ ⁻¹' K) n x₁ = sv P (φ ⁻¹' K) n x₂ := by
  rw [sv_lump h, sv_lump h, hφ]

/-- **If survival splits within a block, no macro chain reproduces it.** -/
theorem no_chain_of_split {φ : X → Y} {P : X → X → ℝ} {K : Set Y} {n : ℕ} {x₁ x₂ : X}
    (hφ : φ x₁ = φ x₂) (hne : sv P (φ ⁻¹' K) n x₁ ≠ sv P (φ ⁻¹' K) n x₂) :
    ¬ ∃ Q : Y → Y → ℝ, ∀ x, sv P (φ ⁻¹' K) n x = sv Q K n (φ x) := by
  rintro ⟨Q, hQ⟩
  exact hne (by rw [hQ x₁, hQ x₂, hφ])

/-- Three micro states: `0` stays put, `1` jumps to `2`, `2` (dead) stays put. -/
noncomputable def Pc : Fin 3 → Fin 3 → ℝ := fun x x' =>
  if x = 1 then (if x' = 2 then 1 else 0) else (if x' = x then 1 else 0)

/-- Viable/dead labelling: `0, 1 ↦ true`, `2 ↦ false`. -/
def φc : Fin 3 → Bool := fun x => if x = 2 then false else true

/-- **Concrete split:** states `0` and `1` are both labelled viable, but one-step survival is 1
from `0` and 0 from `1`. No macro kernel on `Bool` reproduces this. -/
theorem split_instance :
    ¬ ∃ Q : Bool → Bool → ℝ, ∀ x, sv Pc (φc ⁻¹' {true}) 1 x = sv Q {true} 1 (φc x) := by
  refine no_chain_of_split (x₁ := 0) (x₂ := 1) (by decide) ?_
  simp [sv, Pc, φc, Fin.sum_univ_three]

/-- A hidden fair coin: every micro transition has probability 1/4 on `Bool × Bool`. -/
noncomputable def Pu : Bool × Bool → Bool × Bool → ℝ := fun _ _ => 1 / 4

/-- **Non-vacuity:** `Prod.fst` lumps `Pu` onto the fair macro chain, so micro survival in
`fst⁻¹ K` equals macro survival in `K`. -/
theorem lump_instance (K : Set Bool) (n : ℕ) (x : Bool × Bool) :
    Lumpable Prod.fst Pu (fun _ _ => 1 / 2) ∧
    sv Pu (Prod.fst ⁻¹' K) n x = sv (fun _ _ => (1 / 2 : ℝ)) K n x.1 := by
  have hL : Lumpable Prod.fst Pu (fun _ _ => 1 / 2) := by
    intro x y'
    rw [Finset.sum_filter]
    cases y' <;> simp [Pu, Fintype.sum_prod_type] <;> norm_num
  exact ⟨hL, sv_lump hL K n x⟩

/-! ### State-dependent hazards and approximate lumpability -/

theorem sv_nonneg {P : X → X → ℝ} (hP : ∀ x x', 0 ≤ P x x') (K : Set X) (n : ℕ) (x : X) :
    0 ≤ sv P K n x := by
  induction n generalizing x with
  | zero => simp only [sv]; split_ifs <;> norm_num
  | succ n ih => simp only [sv]; split_ifs
                 · exact sum_nonneg fun x' _ => mul_nonneg (hP x x') (ih x')
                 · exact le_rfl

theorem sv_le_one {P : X → X → ℝ} (hP : ∀ x x', 0 ≤ P x x') (hrow : ∀ x, ∑ x', P x x' ≤ 1)
    (K : Set X) (n : ℕ) (x : X) : sv P K n x ≤ 1 := by
  induction n generalizing x with
  | zero => simp only [sv]; split_ifs <;> norm_num
  | succ n ih =>
    simp only [sv]; split_ifs
    · calc ∑ x', P x x' * sv P K n x' ≤ ∑ x', P x x' * 1 :=
            sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (ih x') (hP x x')
        _ ≤ 1 := by simpa using hrow x
    · norm_num

theorem sv_out {P : X → X → ℝ} {K : Set X} (n : ℕ) {x : X} (hx : x ∉ K) : sv P K n x = 0 := by
  cases n <;> simp [sv, hx]

/-- Probability of staying in `K` for one step from `x`. -/
noncomputable def stayP (P : X → X → ℝ) (K : Set X) (x : X) : ℝ :=
  ∑ x', P x x' * (if x' ∈ K then 1 else 0)

/-- **State-dependent hazards, lower bound:** if from every state in `K` the one-step exit
probability is at most `h` (`stayP ≥ 1 − h`), survival is at least `(1 − h)^n` from every
state in `K`. -/
theorem markov_hazard_lower {P : X → X → ℝ} (hP : ∀ x x', 0 ≤ P x x') {K : Set X} {h : ℝ}
    (h1 : h ≤ 1) (hK : ∀ x ∈ K, 1 - h ≤ stayP P K x) (n : ℕ) {x : X} (hx : x ∈ K) :
    (1 - h) ^ n ≤ sv P K n x := by
  induction n generalizing x with
  | zero => simp [sv, hx]
  | succ n ih =>
    simp only [sv, hx, if_true]
    have hpt : ∀ x', (1 - h) ^ n * (if x' ∈ K then 1 else 0) ≤ sv P K n x' := by
      intro x'; split_ifs with h'
      · simpa using ih h'
      · simpa using sv_nonneg hP K n x'
    calc (1 - h) ^ (n + 1) = (1 - h) ^ n * (1 - h) := pow_succ _ _
      _ ≤ (1 - h) ^ n * stayP P K x :=
          mul_le_mul_of_nonneg_left (hK x hx) (pow_nonneg (by linarith) n)
      _ = ∑ x', P x x' * ((1 - h) ^ n * (if x' ∈ K then 1 else 0)) := by
          unfold stayP; rw [mul_sum]; exact sum_congr rfl fun x' _ => by ring
      _ ≤ ∑ x', P x x' * sv P K n x' :=
          sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hpt x') (hP x x')

/-- **State-dependent hazards, upper bound:** if from every state in `K` the exit probability
is at least `q` (`stayP ≤ 1 − q`), survival is at most `(1 − q)^n`, so it dies when `q > 0`. -/
theorem markov_hazard_upper {P : X → X → ℝ} (hP : ∀ x x', 0 ≤ P x x')
    (hrow : ∀ x, ∑ x', P x x' ≤ 1) {K : Set X} {q : ℝ} (hq1 : q ≤ 1)
    (hK : ∀ x ∈ K, stayP P K x ≤ 1 - q) (n : ℕ) (x : X) : sv P K n x ≤ (1 - q) ^ n := by
  induction n generalizing x with
  | zero => simp only [sv]; split_ifs <;> norm_num
  | succ n ih =>
    simp only [sv]; split_ifs with hx
    · have hpt : ∀ x', sv P K n x' ≤ (1 - q) ^ n * (if x' ∈ K then 1 else 0) := by
        intro x'; split_ifs with h'
        · simpa using ih x'
        · rw [sv_out n h']; simp
      calc ∑ x', P x x' * sv P K n x'
          ≤ ∑ x', P x x' * ((1 - q) ^ n * (if x' ∈ K then 1 else 0)) :=
            sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hpt x') (hP x x')
        _ = (1 - q) ^ n * stayP P K x := by
            unfold stayP; rw [mul_sum]; exact sum_congr rfl fun x' _ => by ring
        _ ≤ (1 - q) ^ n * (1 - q) :=
            mul_le_mul_of_nonneg_left (hK x hx) (pow_nonneg (by linarith) n)
        _ = (1 - q) ^ (n + 1) := (pow_succ _ _).symm
    · exact pow_nonneg (by linarith) _

theorem fiber_sum (φ : X → Y) (P : X → X → ℝ) (g : Y → ℝ) (x : X) :
    ∑ x', P x x' * g (φ x') = ∑ y', (∑ x' ∈ univ.filter (fun x' => φ x' = y'), P x x') * g y' := by
  rw [← Finset.sum_fiberwise univ φ (fun x' => P x x' * g (φ x'))]
  refine sum_congr rfl fun y' _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun x' hx' => ?_
  rw [(mem_filter.1 hx').2]

/-- **Approximate lumpability:** if, from every micro state, the block-transition
probabilities differ from the macro kernel by at most `η` in total variation (`ℓ¹`), then
micro and macro survival differ by at most `n η` after `n` steps. With exact lumpability
(`η = 0`) this recovers `sv_lump`. -/
theorem sv_approx_lump {φ : X → Y} {P : X → X → ℝ} {Q : Y → Y → ℝ}
    (hP : ∀ x x', 0 ≤ P x x') (hrow : ∀ x, ∑ x', P x x' ≤ 1)
    (hQ : ∀ y y', 0 ≤ Q y y') (hQrow : ∀ y, ∑ y', Q y y' ≤ 1) {η : ℝ}
    (hη : ∀ x, ∑ y', |∑ x' ∈ univ.filter (fun x' => φ x' = y'), P x x' - Q (φ x) y'| ≤ η)
    (K : Set Y) (n : ℕ) (x : X) :
    |sv P (φ ⁻¹' K) n x - sv Q K n (φ x)| ≤ n * η := by
  have hη0 : 0 ≤ η := (sum_nonneg fun _ _ => abs_nonneg _).trans (hη x)
  induction n generalizing x with
  | zero => simp [sv, Set.mem_preimage]
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
      have h1 : |∑ x', P x x' * (sv P (φ ⁻¹' K) n x' - g (φ x'))| ≤ n * η :=
        calc _ ≤ ∑ x', |P x x' * (sv P (φ ⁻¹' K) n x' - g (φ x'))| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ x', P x x' * (n * η) := sum_le_sum fun x' _ => by
              rw [abs_mul, abs_of_nonneg (hP x x')]
              exact mul_le_mul_of_nonneg_left (ih x') (hP x x')
          _ = (∑ x', P x x') * (n * η) := by rw [sum_mul]
          _ ≤ 1 * (n * η) := mul_le_mul_of_nonneg_right (hrow x) (by positivity)
          _ = n * η := one_mul _
      have h2 : |∑ y', ((∑ x' ∈ univ.filter (fun x' => φ x' = y'), P x x') - Q (φ x) y') * g y'|
          ≤ η :=
        calc _ ≤ ∑ y', |((∑ x' ∈ univ.filter (fun x' => φ x' = y'), P x x') - Q (φ x) y') * g y'| :=
              abs_sum_le_sum_abs _ _
          _ ≤ ∑ y', |(∑ x' ∈ univ.filter (fun x' => φ x' = y'), P x x') - Q (φ x) y'| :=
              sum_le_sum fun y' _ => by
                rw [abs_mul, abs_of_nonneg (sv_nonneg hQ K n y')]
                exact mul_le_of_le_one_right (abs_nonneg _) (sv_le_one hQ hQrow K n y')
          _ ≤ η := hη x
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ n * η + η := add_le_add h1 h2
        _ = ((n + 1 : ℕ) : ℝ) * η := by push_cast; ring
    · simp; positivity

end FiveOrgans.CrossScaleMarkov
