import FiveOrgans.PoissonTail
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# KL confidence sets and a two-sample test for small means (unknown `p`)

`PoissonTail` bounds the tail for a KNOWN mean `p`. A test on data needs the mean unknown.
This module inverts the bound into a confidence set and builds a two-sample test from it.

Setting: `X 0, X 1, …` independent, values in `[0, 1]`, common mean `p > 0`; `S = Σ_{i<N} X i`,
`p̂ = S / N`.

* `poisKL_eq`, `poisKL_cont` — `a ↦ poisKL a p` is continuous (including at `a = 0`).
* `kl_upper` — `P(p̂ ≥ p ∧ N · poisKL p̂ p ≥ L) ≤ e^{−L}`. No monotonicity or root-finding is
  needed: take `a₀ = inf {a ≥ p : N · poisKL a p ≥ L}`. The set is closed, so `a₀` belongs to it
  and every such `p̂` is at least `a₀`; then apply `upper_opt` at `a₀`.
* `lower_zero` — `P(S ≤ 0) ≤ e^{−N p}` (the limit `t → ∞` of `lower_tail`).
* `kl_lower` — `P(p̂ ≤ p ∧ N · poisKL p̂ p ≥ L) ≤ e^{−L}` (sup of the set, `lower_opt` or
  `lower_zero`).
* `kl_conf` — `P(N · poisKL p̂ p ≥ L) ≤ 2 e^{−L}`; `kl_conf_alpha` — with `L = log (2/α)`, the
  set `{q : N · poisKL p̂ q < log (2/α)}` misses `p` with probability at most `α`.
* `kl_two_sample` — two samples (sizes `N₁`, `N₂`, ANY dependence between them) with the same
  mean `p`. The rule "no `q > 0` lies in both KL sets" fires with probability at most `4 e^{−L}`.
  `kl_two_sample_alpha` uses `L = log (4/α)`.

Caveats as before: the counts `N` are fixed (see `RandomCount` for a union over random counts),
and the draws must be independent with a common mean. Nothing here makes logged data i.i.d.
-/

namespace FiveOrgans.PoissonConf
open MeasureTheory ProbabilityTheory Finset Real Filter Topology
open FiveOrgans.PoissonTail

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem poisKL_eq {a p : ℝ} (hp : p ≠ 0) : poisKL a p = p * ((a / p) * log (a / p)) - a + p := by
  unfold poisKL; rw [← mul_assoc, mul_div_cancel₀ a hp]

theorem poisKL_cont {p : ℝ} (hp : p ≠ 0) : Continuous fun a => poisKL a p := by
  simp_rw [poisKL_eq hp]
  exact ((continuous_const.mul (continuous_mul_log.comp (continuous_id.div_const p))).sub
    continuous_id).add continuous_const

theorem poisKL_zero (p : ℝ) : poisKL 0 p = p := by simp [poisKL]

/-- **Upper half of the confidence statement.** -/
theorem kl_upper {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) {N : ℕ} (hN : 0 < N)
    (hp : 0 < p) (L : ℝ) :
    μ.real {ω | p ≤ (∑ i ∈ range N, X i ω) / N ∧ L ≤ N * poisKL ((∑ i ∈ range N, X i ω) / N) p}
      ≤ exp (-L) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  set A : Set ℝ := {a | p ≤ a ∧ L ≤ N * poisKL a p} with hAdef
  by_cases hA : A.Nonempty
  · have hcl : IsClosed A := (isClosed_le continuous_const continuous_id).inter
      (isClosed_le continuous_const (continuous_const.mul (poisKL_cont hp.ne')))
    have hbdd : BddBelow A := ⟨p, fun a ha => ha.1⟩
    have ha0 : sInf A ∈ A := hcl.csInf_mem hA hbdd
    calc _ ≤ μ.real {ω | N * sInf A ≤ ∑ i ∈ range N, X i ω} := by
          refine measureReal_mono (fun ω hω => ?_)
          have h1 : sInf A ≤ (∑ i ∈ range N, X i ω) / N := csInf_le hbdd hω
          rw [le_div_iff₀ hN'] at h1
          show (N : ℝ) * sInf A ≤ ∑ i ∈ range N, X i ω
          linarith
      _ ≤ exp (-(N * poisKL (sInf A) p)) := upper_opt hX hind hr hm N hp ha0.1
      _ ≤ exp (-L) := exp_le_exp.2 (by linarith [ha0.2])
  · calc _ ≤ μ.real (∅ : Set Ω) := measureReal_mono (fun ω hω => (hA ⟨_, hω⟩).elim)
      _ ≤ exp (-L) := by rw [measureReal_empty]; positivity

/-- `P(S ≤ 0) ≤ e^{−N p}`: the `t → ∞` limit of `lower_tail` at `a = 0`. -/
theorem lower_zero {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (N : ℕ) :
    μ.real {ω | ∑ i ∈ range N, X i ω ≤ N * 0} ≤ exp (-(N * p)) := by
  have key : ∀ᶠ t in atTop, μ.real {ω | ∑ i ∈ range N, X i ω ≤ N * 0}
      ≤ exp (N * p * (exp (-t) - 1)) :=
    (eventually_ge_atTop 0).mono fun t ht =>
      (lower_tail hX hind hr hm N 0 ht).trans_eq (by congr 1; ring)
  have tend : Tendsto (fun t : ℝ => exp (N * p * (exp (-t) - 1))) atTop (𝓝 (exp (-(N * p)))) := by
    have := ((tendsto_exp_neg_atTop_nhds_zero.sub_const 1).const_mul ((N : ℝ) * p)).rexp
    convert this using 2; ring_nf
  exact ge_of_tendsto tend key

/-- **Lower half of the confidence statement.** -/
theorem kl_lower {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) {N : ℕ} (hN : 0 < N)
    (hp : 0 < p) (L : ℝ) :
    μ.real {ω | (∑ i ∈ range N, X i ω) / N ≤ p ∧ L ≤ N * poisKL ((∑ i ∈ range N, X i ω) / N) p}
      ≤ exp (-L) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hS0 : ∀ ω, 0 ≤ (∑ i ∈ range N, X i ω) / N := fun ω =>
    div_nonneg (sum_nonneg fun i _ => (hr i ω).1) hN'.le
  set A : Set ℝ := {a | 0 ≤ a ∧ a ≤ p ∧ L ≤ N * poisKL a p} with hAdef
  by_cases hA : A.Nonempty
  · have hcl : IsClosed A := (isClosed_le continuous_const continuous_id).inter
      ((isClosed_le continuous_id continuous_const).inter
        (isClosed_le continuous_const (continuous_const.mul (poisKL_cont hp.ne'))))
    have hbdd : BddAbove A := ⟨p, fun a ha => ha.2.1⟩
    have ha1 : sSup A ∈ A := hcl.csSup_mem hA hbdd
    have hsub : {ω | (∑ i ∈ range N, X i ω) / N ≤ p ∧
        L ≤ N * poisKL ((∑ i ∈ range N, X i ω) / N) p}
        ⊆ {ω | ∑ i ∈ range N, X i ω ≤ N * sSup A} := fun ω hω => by
      have h1 : (∑ i ∈ range N, X i ω) / N ≤ sSup A := le_csSup hbdd ⟨hS0 ω, hω⟩
      rw [div_le_iff₀ hN'] at h1
      show ∑ i ∈ range N, X i ω ≤ (N : ℝ) * sSup A
      linarith
    rcases ha1.1.lt_or_eq with hpos | hzero
    · calc _ ≤ μ.real {ω | ∑ i ∈ range N, X i ω ≤ N * sSup A} := measureReal_mono hsub
        _ ≤ exp (-(N * poisKL (sSup A) p)) := lower_opt hX hind hr hm N hpos ha1.2.1
        _ ≤ exp (-L) := exp_le_exp.2 (by linarith [ha1.2.2])
    · have hL : L ≤ N * p := by have := ha1.2.2; rwa [← hzero, poisKL_zero] at this
      calc _ ≤ μ.real {ω | ∑ i ∈ range N, X i ω ≤ N * sSup A} := measureReal_mono hsub
        _ = μ.real {ω | ∑ i ∈ range N, X i ω ≤ N * 0} := by rw [← hzero]
        _ ≤ exp (-(N * p)) := lower_zero hX hind hr hm N
        _ ≤ exp (-L) := exp_le_exp.2 (by linarith)
  · calc _ ≤ μ.real (∅ : Set Ω) :=
          measureReal_mono (fun ω hω => (hA ⟨_, hS0 ω, hω⟩).elim)
      _ ≤ exp (-L) := by rw [measureReal_empty]; positivity

/-- **KL confidence statement:** `P(N · poisKL p̂ p ≥ L) ≤ 2 e^{−L}`. -/
theorem kl_conf {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) {N : ℕ} (hN : 0 < N)
    (hp : 0 < p) (L : ℝ) :
    μ.real {ω | L ≤ N * poisKL ((∑ i ∈ range N, X i ω) / N) p} ≤ 2 * exp (-L) := by
  calc _ ≤ μ.real ({ω | p ≤ (∑ i ∈ range N, X i ω) / N ∧
              L ≤ N * poisKL ((∑ i ∈ range N, X i ω) / N) p} ∪
            {ω | (∑ i ∈ range N, X i ω) / N ≤ p ∧
              L ≤ N * poisKL ((∑ i ∈ range N, X i ω) / N) p}) := by
          refine measureReal_mono (fun ω hω => ?_)
          rcases le_total p ((∑ i ∈ range N, X i ω) / N) with h | h
          · exact Or.inl ⟨h, hω⟩
          · exact Or.inr ⟨h, hω⟩
    _ ≤ _ + _ := measureReal_union_le _ _
    _ ≤ exp (-L) + exp (-L) := add_le_add (kl_upper hX hind hr hm hN hp L)
          (kl_lower hX hind hr hm hN hp L)
    _ = 2 * exp (-L) := by ring

theorem exp_neg_log {c : ℝ} (hc : 0 < c) : exp (-log c) = 1 / c := by
  rw [exp_neg, exp_log hc, one_div]

/-- **Calibrated confidence set:** with `L = log (2/α)` the set misses `p` w.p. at most `α`. -/
theorem kl_conf_alpha {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) {N : ℕ} (hN : 0 < N)
    (hp : 0 < p) {α : ℝ} (hα : 0 < α) :
    μ.real {ω | log (2 / α) ≤ N * poisKL ((∑ i ∈ range N, X i ω) / N) p} ≤ α := by
  refine (kl_conf hX hind hr hm hN hp _).trans_eq ?_
  rw [exp_neg_log (by positivity)]; field_simp

/-- **Two-sample test.** Two samples with the same mean `p` (any dependence between them).
"No `q > 0` lies in both KL sets" happens with probability at most `4 e^{−L}`. -/
theorem kl_two_sample {X₁ X₂ : ℕ → Ω → ℝ} (hX₁ : ∀ i, Measurable (X₁ i)) (hX₂ : ∀ i, Measurable (X₂ i))
    (hind₁ : iIndepFun X₁ μ) (hind₂ : iIndepFun X₂ μ)
    (hr₁ : ∀ i ω, X₁ i ω ∈ Set.Icc (0 : ℝ) 1) (hr₂ : ∀ i ω, X₂ i ω ∈ Set.Icc (0 : ℝ) 1)
    {p : ℝ} (hm₁ : ∀ i, μ[X₁ i] = p) (hm₂ : ∀ i, μ[X₂ i] = p) {N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hp : 0 < p) (L : ℝ) :
    μ.real {ω | ∀ q, 0 < q → L ≤ N₁ * poisKL ((∑ i ∈ range N₁, X₁ i ω) / N₁) q ∨
                               L ≤ N₂ * poisKL ((∑ i ∈ range N₂, X₂ i ω) / N₂) q}
      ≤ 4 * exp (-L) := by
  calc _ ≤ μ.real ({ω | L ≤ N₁ * poisKL ((∑ i ∈ range N₁, X₁ i ω) / N₁) p} ∪
            {ω | L ≤ N₂ * poisKL ((∑ i ∈ range N₂, X₂ i ω) / N₂) p}) :=
          measureReal_mono (fun ω hω => by simp only [Set.mem_ofPred_eq] at hω; exact hω p hp)
    _ ≤ _ + _ := measureReal_union_le _ _
    _ ≤ 2 * exp (-L) + 2 * exp (-L) := add_le_add (kl_conf hX₁ hind₁ hr₁ hm₁ hN₁ hp L)
          (kl_conf hX₂ hind₂ hr₂ hm₂ hN₂ hp L)
    _ = 4 * exp (-L) := by ring

/-- **Calibrated two-sample test:** `L = log (4/α)` gives false-rejection probability `≤ α`. -/
theorem kl_two_sample_alpha {X₁ X₂ : ℕ → Ω → ℝ} (hX₁ : ∀ i, Measurable (X₁ i))
    (hX₂ : ∀ i, Measurable (X₂ i)) (hind₁ : iIndepFun X₁ μ) (hind₂ : iIndepFun X₂ μ)
    (hr₁ : ∀ i ω, X₁ i ω ∈ Set.Icc (0 : ℝ) 1) (hr₂ : ∀ i ω, X₂ i ω ∈ Set.Icc (0 : ℝ) 1)
    {p : ℝ} (hm₁ : ∀ i, μ[X₁ i] = p) (hm₂ : ∀ i, μ[X₂ i] = p) {N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hp : 0 < p) {α : ℝ} (hα : 0 < α) :
    μ.real {ω | ∀ q, 0 < q → log (4 / α) ≤ N₁ * poisKL ((∑ i ∈ range N₁, X₁ i ω) / N₁) q ∨
                               log (4 / α) ≤ N₂ * poisKL ((∑ i ∈ range N₂, X₂ i ω) / N₂) q}
      ≤ α := by
  refine (kl_two_sample hX₁ hX₂ hind₁ hind₂ hr₁ hr₂ hm₁ hm₂ hN₁ hN₂ hp _).trans_eq ?_
  rw [exp_neg_log (by positivity)]; field_simp

end FiveOrgans.PoissonConf
