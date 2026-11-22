import FiveOrgans.ViabilityStochastic

/-!
# The Skin under random disturbances

`Skin` assumes a worst-case bound `|d| ≤ D`. Here the disturbance at a step is random, with an
arbitrary distribution `p` on a finite outcome space `Ω`.

* `skin_step_safe` — one step of the skin map keeps the band when `|d| ≤ D` and `μK + ρD ≤ K`.
* `exit_le_tail` — **for a skin in its window, the one-step exit probability from any state in
  the band is at most the tail probability `P(|d| > D)`.**
* `exit_ge_push` — conversely, from **every** state in the band the exit probability is at
  least `P(ρ d > (1+μ)K)`: a big enough push breaches any skin.
* `surv_anti` — survival is antitone in the hazard.
* `tail_viable` — with independent steps whose tail probabilities have total `≤ ε`, an
  in-window skin survives with probability `≥ 1 − ε` forever.
* `heavy_tail_dies` — if the push probability is at least `q > 0` every step (e.g. unbounded
  noise with a fixed distribution), every skin, however tight, dies.

Reading: with random disturbances the window `μK + ρD ≤ K` still governs, but only through the
tails. A skin is viable forever iff the probability of disturbances beyond what it absorbs is
summable over time. Fixed unbounded noise (Gaussian, say) kills every skin eventually. Scope:
independent steps, hazards bounded via one-step bounds (the per-step hazard is assumed to obey
the one-step bound, as in `SkinViability`).
-/

namespace FiveOrgans.SkinStochastic
open Finset FiveOrgans.ViabilityStochastic

theorem skin_step_safe {μ ρ K D s d : ℝ} (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ) (hw : μ * K + ρ * D ≤ K)
    (hs : |s| ≤ K) (hd : |d| ≤ D) : |μ * s + ρ * d| ≤ K := by
  calc |μ * s + ρ * d| ≤ |μ * s| + |ρ * d| := abs_add_le _ _
    _ = μ * |s| + ρ * |d| := by rw [abs_mul, abs_mul, abs_of_nonneg hμ, abs_of_nonneg hρ]
    _ ≤ μ * K + ρ * D := add_le_add (mul_le_mul_of_nonneg_left hs hμ) (mul_le_mul_of_nonneg_left hd hρ)
    _ ≤ K := hw

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

open Classical in
/-- Exit probability of one step from state `s` with random disturbance `d`. -/
noncomputable def exitP (p : Ω → ℝ) (μ ρ K s : ℝ) (d : Ω → ℝ) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω => K < |μ * s + ρ * d ω|), p ω

open Classical in
/-- **In-window exit ≤ tail probability.** -/
theorem exit_le_tail (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) {μ ρ K D s : ℝ} (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ)
    (hw : μ * K + ρ * D ≤ K) (hs : |s| ≤ K) (d : Ω → ℝ) :
    exitP p μ ρ K s d ≤ ∑ ω ∈ univ.filter (fun ω => D < |d ω|), p ω := by
  unfold exitP
  apply sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω ⊢
    by_contra h; push_neg at h
    exact absurd (skin_step_safe hμ hρ hw hs h) (not_le.2 hω)
  · intro ω _ _; exact hp ω

open Classical in
/-- **A big enough push breaches any skin from any in-band state.** -/
theorem exit_ge_push (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) {μ ρ K s : ℝ} (hμ : 0 ≤ μ)
    (hs : |s| ≤ K) (d : Ω → ℝ) :
    ∑ ω ∈ univ.filter (fun ω => (1 + μ) * K < ρ * d ω), p ω ≤ exitP p μ ρ K s d := by
  unfold exitP
  apply sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω ⊢
    have h1 : -K ≤ s := (abs_le.1 hs).1
    have h2 : -(μ * K) ≤ μ * s := by nlinarith
    exact lt_of_lt_of_le (by linarith) (le_abs_self _)
  · intro ω _ _; exact hp ω

/-- Survival is antitone in the hazard. -/
theorem surv_anti {a b : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hab : ∀ i, a i ≤ b i) (n : ℕ) : surv b n ≤ surv a n := by
  induction n with
  | zero => simp [surv]
  | succ n ih =>
    rw [surv_succ, surv_succ]
    exact mul_le_mul ih (by linarith [hab n]) (by linarith [(hb n).2]) (surv_mem a ha n).1

/-- **Summable tails: an in-window skin survives with probability `≥ 1 − ε` forever.** Here
`h i` is the step-`i` hazard and `t i` the tail probability `P(|d_i| > D)`; `exit_le_tail`
gives `h i ≤ t i`. -/
theorem tail_viable {h t : ℕ → ℝ} (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) (hht : ∀ i, h i ≤ t i)
    {ε : ℝ} (ht : ∀ n, ∑ i ∈ range n, t i ≤ ε) (n : ℕ) : 1 - ε ≤ surv h n :=
  budget_viable h hh (fun m => (sum_le_sum fun i _ => hht i).trans (ht m)) n

/-- **Persistent push probability kills every skin.** -/
theorem heavy_tail_dies {h : ℕ → ℝ} (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) {q : ℝ} (hq : 0 < q)
    (hqh : ∀ i, q ≤ h i) {ε : ℝ} (hε : ε < 1) : ∃ n, surv h n < 1 - ε := by
  have hq1 : q ≤ 1 := (hqh 0).trans (hh 0).2
  obtain ⟨n, hn⟩ := const_hazard_dies hq hq1 hε
  exact ⟨n, lt_of_le_of_lt (surv_anti (fun _ => ⟨hq.le, hq1⟩) hh hqh n) hn⟩

end FiveOrgans.SkinStochastic
