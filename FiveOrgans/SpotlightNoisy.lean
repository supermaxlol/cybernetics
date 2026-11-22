import FiveOrgans.Spotlight
import Mathlib.Algebra.BigOperators.Fin

/-!
# The Spotlight with estimated relevance

The agent does not see true relevance `v`; it sees estimates `u` with
`|u i - v i| ≤ e` for every item, and points the spotlight at the item `j`
with the highest *estimate*.

Results.
* `noisy_pick_regret` — the chosen item is within `2e` of the best true item.
* `noisy_spot_near_optimal` — the spotlight loses at most `2Ce` against the best
  allocation (`spot_optimal`).
* `noisy_spot_beats_uniform` — it still strictly beats an even spread whenever the best
  item's margin over the average exceeds `2e`: `(v_best - 2e) * n > ∑ v`.
* `noisy_spot_can_lose` — the margin condition is needed: with two items, true relevance
  `(1, 0)` and estimates `(2/5, 3/5)` (error `3/5`), the spotlight goes to the worse item
  and does strictly worse than an even spread.

Reading: selection pays only when the Watcher-like estimate of relevance is accurate
relative to how uneven the world is. Toy model: worst-case bounded error, known `e`.
-/

namespace FiveOrgans.SpotlightNoisy
open Finset FiveOrgans.Spotlight

variable {n : ℕ}

theorem noisy_pick_regret {u v : Fin n → ℝ} {e : ℝ} (hu : ∀ i, |u i - v i| ≤ e)
    {j : Fin n} (hj : ∀ i, u i ≤ u j) (i : Fin n) : v i ≤ v j + 2 * e := by
  have h1 := abs_le.mp (hu i)
  have h2 := abs_le.mp (hu j)
  linarith [hj i, h1.1, h2.2]

theorem noisy_spot_near_optimal {C e : ℝ} (hC : 0 ≤ C) {u v : Fin n → ℝ}
    (hu : ∀ i, |u i - v i| ≤ e) {j : Fin n} (hj : ∀ i, u i ≤ u j) (i : Fin n) :
    payoff (spot C i) v - 2 * C * e ≤ payoff (spot C j) v := by
  rw [spot_payoff, spot_payoff]
  nlinarith [noisy_pick_regret hu hj i]

theorem noisy_spot_beats_uniform {C e : ℝ} (hC : 0 < C) {u v : Fin n → ℝ}
    (hu : ∀ i, |u i - v i| ≤ e) {j : Fin n} (hj : ∀ i, u i ≤ u j) {b : Fin n}
    (hn : (0 : ℝ) < n) (hmargin : (v b - 2 * e) * n > ∑ i, v i) :
    payoff (uniform C n) v < payoff (spot C j) v := by
  have hr := noisy_pick_regret hu hj b
  rw [spot_payoff, uniform_payoff, div_mul_eq_mul_div, div_lt_iff₀ hn]
  have : (v b - 2 * e) * n ≤ v j * n := mul_le_mul_of_nonneg_right (by linarith) hn.le
  nlinarith [mul_lt_mul_of_pos_left (lt_of_lt_of_le hmargin this) hC]

/-- The margin condition cannot be dropped. -/
theorem noisy_spot_can_lose :
    let v : Fin 2 → ℝ := ![1, 0]
    let u : Fin 2 → ℝ := ![2 / 5, 3 / 5]
    (∀ i, |u i - v i| ≤ 3 / 5) ∧ (∀ i, u i ≤ u 1) ∧
      payoff (spot 1 1) v < payoff (uniform 1 2) v := by
  refine ⟨?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num [abs_le]
  · intro i; fin_cases i <;> norm_num
  · rw [spot_payoff, uniform_payoff]; norm_num [Fin.sum_univ_two]

end FiveOrgans.SpotlightNoisy
