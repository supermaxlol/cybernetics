import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith

/-!
# The Spotlight: selection under a capacity limit

`n` items carry task relevance `v i`. The agent has attention capacity `C`: weights
`w i ≥ 0` with `∑ w i ≤ C`. Payoff = `∑ w i * v i`.

Results.
* `payoff_le` — no allocation can beat `C * max v`.
* `spot_optimal` — putting all capacity on the most relevant item attains it.
* `spot_minus_uniform` — spotlight minus even spread `= (C/n) ∑ (v_max - v i)`.
* `spot_beats_uniform` — strictly better whenever relevance is uneven.
* `misdirected_spotlight` — a spotlight on a below-average item is strictly **worse**
  than no spotlight. Selection only pays if it selects the right thing.

Toy model: linear payoff, known relevances. Unknown relevance: `SpotlightNoisy`;
information cost (entropy, rational inattention) and random error: `SpotlightEntropy`.
-/

namespace FiveOrgans.Spotlight
open Finset

variable {n : ℕ}

def payoff (w v : Fin n → ℝ) : ℝ := ∑ i, w i * v i

def Feasible (C : ℝ) (w : Fin n → ℝ) : Prop := (∀ i, 0 ≤ w i) ∧ ∑ i, w i ≤ C

theorem payoff_le {C M : ℝ} {w v : Fin n → ℝ} (hw : Feasible C w) (hM : 0 ≤ M)
    (hv : ∀ i, v i ≤ M) : payoff w v ≤ C * M := by
  unfold payoff
  calc ∑ i, w i * v i ≤ ∑ i, w i * M :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hv i) (hw.1 i)
    _ = (∑ i, w i) * M := by rw [sum_mul]
    _ ≤ C * M := mul_le_mul_of_nonneg_right hw.2 hM

/-- All capacity on item `j`. -/
def spot (C : ℝ) (j : Fin n) : Fin n → ℝ := fun i => if i = j then C else 0

theorem spot_feasible {C : ℝ} (hC : 0 ≤ C) (j : Fin n) : Feasible C (spot C j) :=
  ⟨fun i => by unfold spot; split_ifs <;> linarith, by simp [spot]⟩

theorem spot_payoff (C : ℝ) (j : Fin n) (v : Fin n → ℝ) : payoff (spot C j) v = C * v j := by
  simp [payoff, spot, ite_mul]

theorem spot_optimal {C : ℝ} {v : Fin n → ℝ} {j : Fin n} (hmax : ∀ i, v i ≤ v j)
    (hj : 0 ≤ v j) {w : Fin n → ℝ} (hw : Feasible C w) :
    payoff w v ≤ payoff (spot C j) v := by
  rw [spot_payoff]; exact payoff_le hw hj hmax

/-- Capacity spread evenly (no spotlight). -/
noncomputable def uniform (C : ℝ) (n : ℕ) : Fin n → ℝ := fun _ => C / n

theorem uniform_payoff (C : ℝ) (v : Fin n → ℝ) :
    payoff (uniform C n) v = C / n * ∑ i, v i := by
  simp [payoff, uniform, mul_sum]

theorem spot_minus_uniform (C : ℝ) (v : Fin n → ℝ) (j : Fin n) (hn : (n : ℝ) ≠ 0) :
    payoff (spot C j) v - payoff (uniform C n) v = C / n * ∑ i, (v j - v i) := by
  rw [spot_payoff, uniform_payoff, sum_sub_distrib]
  simp
  field_simp

theorem spot_beats_uniform {C : ℝ} (hC : 0 < C) {v : Fin n → ℝ} {j : Fin n}
    (hmax : ∀ i, v i ≤ v j) {i₀ : Fin n} (hlt : v i₀ < v j) :
    payoff (uniform C n) v < payoff (spot C j) v := by
  have hn : (0 : ℝ) < n := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) i₀.isLt
  have hs : 0 < ∑ i, (v j - v i) :=
    sum_pos' (fun i _ => sub_nonneg.mpr (hmax i)) ⟨i₀, mem_univ _, sub_pos.mpr hlt⟩
  have key := spot_minus_uniform C v j hn.ne'
  have : 0 < C / n * ∑ i, (v j - v i) := mul_pos (div_pos hC hn) hs
  linarith

/-- Attending to a below-average item is worse than not selecting at all. -/
theorem misdirected_spotlight {C : ℝ} (hC : 0 < C) {v : Fin n → ℝ} {j : Fin n}
    (hn : (0 : ℝ) < n) (h : v j * n < ∑ i, v i) :
    payoff (spot C j) v < payoff (uniform C n) v := by
  rw [spot_payoff, uniform_payoff, div_mul_eq_mul_div, lt_div_iff₀ hn]
  nlinarith [mul_lt_mul_of_pos_left h hC]

end FiveOrgans.Spotlight
