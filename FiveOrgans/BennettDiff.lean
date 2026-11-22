import FiveOrgans.BernKL

/-!
# Direct two-sample difference test with a variance-adaptive (Bennett / Poisson) tail

`BernKL.kl_two_sample_bern` rejects when two KL confidence sets do not overlap. Interval overlap
needs a gap of about `r₁ + r₂` rather than `√(r₁² + r₂²)` (simulation: `analysis/SIM_KL_2026-11-22.md`).
Here the statistic is the difference itself.

* `wtail` — for independent `[0,1]` variables with mean `p` and ANY real weights `d i`:
  `P(A ≤ Σ dᵢ (Xᵢ − p)) ≤ exp (−A + p Σ φ(dᵢ))`, `φ x = eˣ − 1 − x ≥ 0` (Poisson/Bennett mgf).
* `wtail_flip` — the same with `1 − X`: proxy `1 − p` and `φ(−dᵢ)`.
* `scaled_tail` — weights `c` summing to 0, any scale `s`, orientation picked by `p ≤ 1/2`:
  `P(A + bnd c n p s ≤ s · Σ cᵢ Xᵢ) ≤ e^{−A}`. The statistic `Σ cᵢ Xᵢ` does not involve `p`.
* `bennett_test` — `p` unknown: reject when, for every `q ∈ (0,1)`, either `q` is outside the
  pooled Bernoulli-KL confidence set or the scaled statistic exceeds the `q`-threshold (scales
  `su q`, `sl q` are any functions of `q` fixed in advance). False rejection `≤ 2e^{−L} + 2e^{−A}`.
* `tw`, `tw_sum`, `tw_stat`, `bennett_two_sample` — weights `1/N₁` on the first `N₁` draws and
  `−1/N₂` on the next `N₂`: the statistic is `p̂₁ − p̂₂`.

* `psi`, `wtail_bern`, `scaled_tail_bern`, `bern_diff_test`, `bern_diff_two_sample` — the same
  with the exact Bernoulli log-mgf `ψ_q(x) = log(1 + q(eˣ−1)) − qx` (variance `q(1−q)`) in place of
  the Poisson proxy (variance `min(q, 1−q)`). This is the version to use: the Poisson proxy is
  worse than Hoeffding at `q = 1/2`; `ψ` is not.

Assumption, stronger than `kl_two_sample_bern`: ALL `N₁ + N₂` draws are independent with one
common mean (the null). It does not make logged data i.i.d.
-/

namespace FiveOrgans.BennettDiff
open MeasureTheory ProbabilityTheory Finset Real
open FiveOrgans.PoissonTail FiveOrgans.PoissonFlip FiveOrgans.BernKL

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `φ x = eˣ − 1 − x`. -/
noncomputable def phi (x : ℝ) : ℝ := exp x - 1 - x

theorem phi_nonneg (x : ℝ) : 0 ≤ phi x := by unfold phi; linarith [add_one_le_exp x]

theorem wtail {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p)
    (d : ℕ → ℝ) (n : ℕ) (A : ℝ) :
    μ.real {ω | A ≤ ∑ i ∈ range n, d i * (X i ω - p)}
      ≤ exp (-A + p * ∑ i ∈ range n, phi (d i)) := by
  have hY : ∀ i, Measurable (fun ω => d i * X i ω) := fun i => (hX i).const_mul (d i)
  have hindY : iIndepFun (fun i ω => d i * X i ω) μ :=
    hind.comp (fun i x => d i * x) (fun i => measurable_const.mul measurable_id)
  have hmgf : mgf (∑ i ∈ range n, fun ω => d i * X i ω) μ 1
      ≤ exp (p * ∑ i ∈ range n, (exp (d i) - 1)) := by
    rw [hindY.mgf_sum hY]
    calc ∏ i ∈ range n, mgf (fun ω => d i * X i ω) μ 1
        ≤ ∏ i ∈ range n, exp (p * (exp (d i) - 1)) := by
          refine Finset.prod_le_prod₀ (h0 := fun i _ => mgf_nonneg) (h1 := fun i _ => ?_)
          have : mgf (fun ω => d i * X i ω) μ 1 = mgf (X i) μ (d i) := by simp [mgf]
          rw [this]; exact mgf_le (hX i) (hr i) (hm i) (d i)
      _ = exp (p * ∑ i ∈ range n, (exp (d i) - 1)) := by rw [← exp_sum, mul_sum]
  have hint : Integrable (fun ω => exp (1 * (∑ i ∈ range n, fun ω => d i * X i ω) ω)) μ := by
    refine Integrable.of_bound (C := exp (∑ i ∈ range n, |d i|)) (by fun_prop)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.2
    rw [one_mul, Finset.sum_apply]
    refine sum_le_sum fun i _ => ?_
    have h := hr i ω
    show d i * X i ω ≤ |d i|
    calc d i * X i ω ≤ |d i * X i ω| := le_abs_self _
      _ = |d i| * X i ω := by rw [abs_mul, abs_of_nonneg h.1]
      _ ≤ |d i| * 1 := mul_le_mul_of_nonneg_left h.2 (abs_nonneg _)
      _ = |d i| := mul_one _
  have h := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ range n, fun ω => d i * X i ω)
    (A + p * ∑ i ∈ range n, d i) zero_le_one hint
  have e : ∀ ω, ∑ i ∈ range n, d i * (X i ω - p)
      = ∑ i ∈ range n, d i * X i ω - p * ∑ i ∈ range n, d i := fun ω => by
    rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun i _ => by ring
  have hset : {ω | A ≤ ∑ i ∈ range n, d i * (X i ω - p)}
      = {ω | A + p * ∑ i ∈ range n, d i ≤ (∑ i ∈ range n, fun ω => d i * X i ω) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.sum_apply, e ω]
    constructor <;> intro h <;> linarith
  rw [hset]
  refine h.trans ?_
  calc exp (-1 * (A + p * ∑ i ∈ range n, d i)) * mgf (∑ i ∈ range n, fun ω => d i * X i ω) μ 1
      ≤ exp (-1 * (A + p * ∑ i ∈ range n, d i)) * exp (p * ∑ i ∈ range n, (exp (d i) - 1)) :=
        mul_le_mul_of_nonneg_left hmgf (exp_pos _).le
    _ = exp (-A + p * ∑ i ∈ range n, phi (d i)) := by
        rw [← exp_add]; congr 1; simp only [phi, sum_sub_distrib]; ring

/-- **Flipped orientation:** proxy `1 − p`, weights negated inside `φ`. -/
theorem wtail_flip {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p)
    (d : ℕ → ℝ) (n : ℕ) (A : ℝ) :
    μ.real {ω | A ≤ ∑ i ∈ range n, d i * (X i ω - p)}
      ≤ exp (-A + (1 - p) * ∑ i ∈ range n, phi (-d i)) := by
  have e : ∀ ω, ∑ i ∈ range n, -d i * ((1 - X i ω) - (1 - p))
      = ∑ i ∈ range n, d i * (X i ω - p) := fun ω => sum_congr rfl fun i _ => by ring
  have h := wtail (flip_measurable hX) (flip_indep hind) (flip_range hr) (flip_mean hX hr hm)
    (fun i => -d i) n A
  simpa only [e] using h

/-- Variance proxy and orientation chosen by `q`. -/
noncomputable def bnd (c : ℕ → ℝ) (n : ℕ) (q s : ℝ) : ℝ :=
  if q ≤ 1 / 2 then q * ∑ i ∈ range n, phi (s * c i) else (1 - q) * ∑ i ∈ range n, phi (-(s * c i))

theorem scaled_tail {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p)
    (c : ℕ → ℝ) (n : ℕ) (hc : ∑ i ∈ range n, c i = 0) (s A : ℝ) :
    μ.real {ω | A + bnd c n p s ≤ s * ∑ i ∈ range n, c i * X i ω} ≤ exp (-A) := by
  have e : ∀ ω, s * ∑ i ∈ range n, c i * X i ω = ∑ i ∈ range n, s * c i * (X i ω - p) := by
    intro ω
    rw [show ∑ i ∈ range n, s * c i * (X i ω - p)
        = s * ∑ i ∈ range n, c i * X i ω - s * p * ∑ i ∈ range n, c i by
      rw [mul_sum, mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun i _ => by ring, hc]
    ring
  have hs : ∀ B, {ω | A + B ≤ s * ∑ i ∈ range n, c i * X i ω}
      = {ω | A + B ≤ ∑ i ∈ range n, s * c i * (X i ω - p)} := fun B => by
    ext ω; simp only [Set.mem_ofPred_eq, e ω]
  unfold bnd
  split_ifs with hq
  · rw [hs]
    exact (wtail hX hind hr hm (fun i => s * c i) n _).trans_eq (by congr 1; ring)
  · rw [hs]
    exact (wtail_flip hX hind hr hm (fun i => s * c i) n _).trans_eq (by congr 1; ring)

/-- **Direct difference test, unknown `p`.** `D ω = Σ cᵢ Xᵢ ω` with `Σ cᵢ = 0`; scales `su, sl`
are any functions of `q` fixed in advance (typically `su > 0` for the upper tail, `sl < 0` for
the lower). Under the null, false rejection `≤ 2e^{−L} + 2e^{−A}`. -/
theorem bennett_test {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (hp : 0 < p)
    (hp1 : p < 1) (c : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (hc : ∑ i ∈ range n, c i = 0)
    (D : Ω → ℝ) (hD : ∀ ω, D ω = ∑ i ∈ range n, c i * X i ω) (su sl : ℝ → ℝ) (L A : ℝ) :
    μ.real {ω | ∀ q, 0 < q → q < 1 → L ≤ n * binKL ((∑ i ∈ range n, X i ω) / n) q ∨
        A + bnd c n q (su q) ≤ su q * D ω ∨ A + bnd c n q (sl q) ≤ sl q * D ω}
      ≤ 2 * exp (-L) + 2 * exp (-A) := by
  calc _ ≤ μ.real (({ω | L ≤ n * binKL ((∑ i ∈ range n, X i ω) / n) p} ∪
            {ω | A + bnd c n p (su p) ≤ su p * ∑ i ∈ range n, c i * X i ω}) ∪
            {ω | A + bnd c n p (sl p) ≤ sl p * ∑ i ∈ range n, c i * X i ω}) :=
          measureReal_mono fun ω hω => by
            simp only [Set.mem_ofPred_eq] at hω
            rcases hω p hp hp1 with h | h | h
            · exact Or.inl (Or.inl h)
            · rw [hD] at h; exact Or.inl (Or.inr h)
            · rw [hD] at h; exact Or.inr h
    _ ≤ μ.real (_ ∪ _) + μ.real _ := measureReal_union_le _ _
    _ ≤ (2 * exp (-L) + exp (-A)) + exp (-A) :=
        add_le_add ((measureReal_union_le _ _).trans (add_le_add
          (kl_conf_bern hX hind hr hm hn hp hp1 L) (scaled_tail hX hind hr hm c n hc (su p) A)))
          (scaled_tail hX hind hr hm c n hc (sl p) A)
    _ = 2 * exp (-L) + 2 * exp (-A) := by ring

/-- Two-sample weights: `1/N₁` on draws `0..N₁−1`, `−1/N₂` on draws `N₁..N₁+N₂−1`. -/
noncomputable def tw (N₁ N₂ : ℕ) (i : ℕ) : ℝ := if i < N₁ then 1 / N₁ else -(1 / N₂)

theorem tw_stat (N₁ N₂ : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ range (N₁ + N₂), tw N₁ N₂ i * f i
      = (∑ i ∈ range N₁, f i) / N₁ - (∑ j ∈ range N₂, f (N₁ + j)) / N₂ := by
  rw [sum_range_add]
  have h1 : ∑ i ∈ range N₁, tw N₁ N₂ i * f i = (∑ i ∈ range N₁, f i) / N₁ := by
    rw [sum_div]; exact sum_congr rfl fun i hi => by
      rw [tw]; split_ifs with h
      · ring
      · exact absurd (mem_range.1 hi) h
  have h2 : ∑ j ∈ range N₂, tw N₁ N₂ (N₁ + j) * f (N₁ + j)
      = -((∑ j ∈ range N₂, f (N₁ + j)) / N₂) := by
    rw [sum_div, ← sum_neg_distrib]
    exact sum_congr rfl fun j _ => by
      rw [tw]; split_ifs with h
      · omega
      · ring
  rw [h1, h2]; ring

theorem tw_sum {N₁ N₂ : ℕ} (h₁ : 0 < N₁) (h₂ : 0 < N₂) : ∑ i ∈ range (N₁ + N₂), tw N₁ N₂ i = 0 := by
  have h := tw_stat N₁ N₂ (fun _ => (1 : ℝ))
  simp only [mul_one, sum_const, card_range, nsmul_eq_mul] at h
  rw [h, div_self (Nat.cast_ne_zero.2 h₁.ne'), div_self (Nat.cast_ne_zero.2 h₂.ne'), sub_self]

/-- **Two-sample direct test.** Statistic `p̂₁ − p̂₂` (draws `0..N₁−1` vs `N₁..N₁+N₂−1`),
KL confidence set from the pooled sample. False rejection `≤ 2e^{−L} + 2e^{−A}`. -/
theorem bennett_two_sample {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ}
    (hm : ∀ i, μ[X i] = p) (hp : 0 < p) (hp1 : p < 1) {N₁ N₂ : ℕ} (h₁ : 0 < N₁) (h₂ : 0 < N₂)
    (su sl : ℝ → ℝ) (L A : ℝ) :
    μ.real {ω | ∀ q, 0 < q → q < 1 →
        L ≤ (N₁ + N₂ : ℕ) * binKL ((∑ i ∈ range (N₁ + N₂), X i ω) / (N₁ + N₂ : ℕ)) q ∨
        A + bnd (tw N₁ N₂) (N₁ + N₂) q (su q) ≤
          su q * ((∑ i ∈ range N₁, X i ω) / N₁ - (∑ j ∈ range N₂, X (N₁ + j) ω) / N₂) ∨
        A + bnd (tw N₁ N₂) (N₁ + N₂) q (sl q) ≤
          sl q * ((∑ i ∈ range N₁, X i ω) / N₁ - (∑ j ∈ range N₂, X (N₁ + j) ω) / N₂)}
      ≤ 2 * exp (-L) + 2 * exp (-A) :=
  bennett_test hX hind hr hm hp hp1 (tw N₁ N₂) (by omega) (tw_sum h₁ h₂)
    (fun ω => (∑ i ∈ range N₁, X i ω) / N₁ - (∑ j ∈ range N₂, X (N₁ + j) ω) / N₂)
    (fun ω => (tw_stat N₁ N₂ (fun i => X i ω)).symm) su sl L A

/-! ### Exact Bernoulli log-mgf proxy (variance `q(1−q)`)

`ψ_q(x) = log(1 + q(eˣ − 1)) − q x` is the log-mgf of a centred Bernoulli(q). By `mgf_le_bern`
it bounds every `[0,1]` variable with mean `q`. Near 0, `ψ_q(x) ≈ q(1−q)x²/2`, so it is never worse
than Hoeffding's `x²/8`, and much better for rare outcomes. -/

/-- `ψ_q(x) = log(1 + q(eˣ − 1)) − q x`. -/
noncomputable def psi (q x : ℝ) : ℝ := log (1 + q * (exp x - 1)) - q * x

theorem wtail_bern {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (hp : 0 < p)
    (hp1 : p < 1) (d : ℕ → ℝ) (n : ℕ) (A : ℝ) :
    μ.real {ω | A ≤ ∑ i ∈ range n, d i * (X i ω - p)}
      ≤ exp (-A + ∑ i ∈ range n, psi p (d i)) := by
  have hY : ∀ i, Measurable (fun ω => d i * X i ω) := fun i => (hX i).const_mul (d i)
  have hindY : iIndepFun (fun i ω => d i * X i ω) μ :=
    hind.comp (fun i x => d i * x) (fun i => measurable_const.mul measurable_id)
  have hpos : ∀ x, 0 < 1 + p * (exp x - 1) := fun x => bern_pos hp.le hp1.le x (Or.inl hp)
  have hmgf : mgf (∑ i ∈ range n, fun ω => d i * X i ω) μ 1
      ≤ exp (∑ i ∈ range n, log (1 + p * (exp (d i) - 1))) := by
    rw [hindY.mgf_sum hY, exp_sum]
    refine Finset.prod_le_prod₀ (h0 := fun i _ => mgf_nonneg) (h1 := fun i _ => ?_)
    have : mgf (fun ω => d i * X i ω) μ 1 = mgf (X i) μ (d i) := by simp [mgf]
    rw [this, exp_log (hpos _)]; exact mgf_le_bern (hX i) (hr i) (hm i) (d i)
  have hint : Integrable (fun ω => exp (1 * (∑ i ∈ range n, fun ω => d i * X i ω) ω)) μ := by
    refine Integrable.of_bound (C := exp (∑ i ∈ range n, |d i|)) (by fun_prop)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.2
    rw [one_mul, Finset.sum_apply]
    refine sum_le_sum fun i _ => ?_
    have h := hr i ω
    show d i * X i ω ≤ |d i|
    calc d i * X i ω ≤ |d i * X i ω| := le_abs_self _
      _ = |d i| * X i ω := by rw [abs_mul, abs_of_nonneg h.1]
      _ ≤ |d i| * 1 := mul_le_mul_of_nonneg_left h.2 (abs_nonneg _)
      _ = |d i| := mul_one _
  have h := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ range n, fun ω => d i * X i ω)
    (A + p * ∑ i ∈ range n, d i) zero_le_one hint
  have e : ∀ ω, ∑ i ∈ range n, d i * (X i ω - p)
      = ∑ i ∈ range n, d i * X i ω - p * ∑ i ∈ range n, d i := fun ω => by
    rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun i _ => by ring
  have hset : {ω | A ≤ ∑ i ∈ range n, d i * (X i ω - p)}
      = {ω | A + p * ∑ i ∈ range n, d i ≤ (∑ i ∈ range n, fun ω => d i * X i ω) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.sum_apply, e ω]
    constructor <;> intro h <;> linarith
  rw [hset]
  refine h.trans ?_
  calc exp (-1 * (A + p * ∑ i ∈ range n, d i)) * mgf (∑ i ∈ range n, fun ω => d i * X i ω) μ 1
      ≤ exp (-1 * (A + p * ∑ i ∈ range n, d i)) *
          exp (∑ i ∈ range n, log (1 + p * (exp (d i) - 1))) :=
        mul_le_mul_of_nonneg_left hmgf (exp_pos _).le
    _ = exp (-A + ∑ i ∈ range n, psi p (d i)) := by
        rw [← exp_add]; congr 1; simp only [psi, sum_sub_distrib, ← mul_sum]; ring

theorem scaled_tail_bern {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (hp : 0 < p)
    (hp1 : p < 1) (c : ℕ → ℝ) (n : ℕ) (hc : ∑ i ∈ range n, c i = 0) (s A : ℝ) :
    μ.real {ω | A + ∑ i ∈ range n, psi p (s * c i) ≤ s * ∑ i ∈ range n, c i * X i ω}
      ≤ exp (-A) := by
  have e : ∀ ω, s * ∑ i ∈ range n, c i * X i ω = ∑ i ∈ range n, s * c i * (X i ω - p) := by
    intro ω
    rw [show ∑ i ∈ range n, s * c i * (X i ω - p)
        = s * ∑ i ∈ range n, c i * X i ω - s * p * ∑ i ∈ range n, c i by
      rw [mul_sum, mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun i _ => by ring, hc]
    ring
  have hs : {ω | A + ∑ i ∈ range n, psi p (s * c i) ≤ s * ∑ i ∈ range n, c i * X i ω}
      = {ω | A + ∑ i ∈ range n, psi p (s * c i) ≤ ∑ i ∈ range n, s * c i * (X i ω - p)} := by
    ext ω; simp only [Set.mem_ofPred_eq, e ω]
  rw [hs]
  exact (wtail_bern hX hind hr hm hp hp1 (fun i => s * c i) n _).trans_eq (by congr 1; ring)

/-- **Direct difference test with the Bernoulli proxy, unknown `p`.** As `bennett_test`, with
threshold `A + Σ ψ_q(s cᵢ)`. False rejection `≤ 2e^{−L} + 2e^{−A}`. -/
theorem bern_diff_test {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (hp : 0 < p)
    (hp1 : p < 1) (c : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (hc : ∑ i ∈ range n, c i = 0)
    (D : Ω → ℝ) (hD : ∀ ω, D ω = ∑ i ∈ range n, c i * X i ω) (su sl : ℝ → ℝ) (L A : ℝ) :
    μ.real {ω | ∀ q, 0 < q → q < 1 → L ≤ n * binKL ((∑ i ∈ range n, X i ω) / n) q ∨
        A + ∑ i ∈ range n, psi q (su q * c i) ≤ su q * D ω ∨
        A + ∑ i ∈ range n, psi q (sl q * c i) ≤ sl q * D ω}
      ≤ 2 * exp (-L) + 2 * exp (-A) := by
  calc _ ≤ μ.real (({ω | L ≤ n * binKL ((∑ i ∈ range n, X i ω) / n) p} ∪
            {ω | A + ∑ i ∈ range n, psi p (su p * c i) ≤ su p * ∑ i ∈ range n, c i * X i ω}) ∪
            {ω | A + ∑ i ∈ range n, psi p (sl p * c i) ≤ sl p * ∑ i ∈ range n, c i * X i ω}) :=
          measureReal_mono fun ω hω => by
            simp only [Set.mem_ofPred_eq] at hω
            rcases hω p hp hp1 with h | h | h
            · exact Or.inl (Or.inl h)
            · rw [hD] at h; exact Or.inl (Or.inr h)
            · rw [hD] at h; exact Or.inr h
    _ ≤ μ.real (_ ∪ _) + μ.real _ := measureReal_union_le _ _
    _ ≤ (2 * exp (-L) + exp (-A)) + exp (-A) :=
        add_le_add ((measureReal_union_le _ _).trans (add_le_add
          (kl_conf_bern hX hind hr hm hn hp hp1 L)
          (scaled_tail_bern hX hind hr hm hp hp1 c n hc (su p) A)))
          (scaled_tail_bern hX hind hr hm hp hp1 c n hc (sl p) A)
    _ = 2 * exp (-L) + 2 * exp (-A) := by ring

/-- **Two-sample direct test, Bernoulli proxy.** Statistic `p̂₁ − p̂₂`. -/
theorem bern_diff_two_sample {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ}
    (hm : ∀ i, μ[X i] = p) (hp : 0 < p) (hp1 : p < 1) {N₁ N₂ : ℕ} (h₁ : 0 < N₁) (h₂ : 0 < N₂)
    (su sl : ℝ → ℝ) (L A : ℝ) :
    μ.real {ω | ∀ q, 0 < q → q < 1 →
        L ≤ (N₁ + N₂ : ℕ) * binKL ((∑ i ∈ range (N₁ + N₂), X i ω) / (N₁ + N₂ : ℕ)) q ∨
        A + ∑ i ∈ range (N₁ + N₂), psi q (su q * tw N₁ N₂ i) ≤
          su q * ((∑ i ∈ range N₁, X i ω) / N₁ - (∑ j ∈ range N₂, X (N₁ + j) ω) / N₂) ∨
        A + ∑ i ∈ range (N₁ + N₂), psi q (sl q * tw N₁ N₂ i) ≤
          sl q * ((∑ i ∈ range N₁, X i ω) / N₁ - (∑ j ∈ range N₂, X (N₁ + j) ω) / N₂)}
      ≤ 2 * exp (-L) + 2 * exp (-A) :=
  bern_diff_test hX hind hr hm hp hp1 (tw N₁ N₂) (by omega) (tw_sum h₁ h₂)
    (fun ω => (∑ i ∈ range N₁, X i ω) / N₁ - (∑ j ∈ range N₂, X (N₁ + j) ω) / N₂)
    (fun ω => (tw_stat N₁ N₂ (fun i => X i ω)).symm) su sl L A

end FiveOrgans.BennettDiff
