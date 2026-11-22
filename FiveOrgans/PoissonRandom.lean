import FiveOrgans.PoissonConf
import FiveOrgans.RandomCount

/-!
# KL tests with random counts

`PoissonConf` treats the counts `N` as fixed. In a Markov chain the visit counts are random
and can depend on the data. As in `RandomCount`, the fix is a union bound over every count the
sample allows. The KL two-sample test needs NO independence between its two samples, so the
union runs over each sample's counts separately: the cost is `|S|`, not `|S|²`.

* `kl_conf_random` — any random count `N ω ∈ S` (positive):
  `P(N · poisKL(p̂_N, p) ≥ L) ≤ |S| · 2 e^{−L}`.
* `kl_conf_random_alpha` — `S = {1,…,T}`, `L = log (2T/α)`: miss probability `≤ α`.
* `kl_two_sample_random` — two tables with the same mean `p`, random counts `N₁ ω, N₂ ω ∈ S`
  (any dependence on anything): "no `q > 0` in both KL sets" has probability `≤ 4 |S| e^{−L}`.
* `kl_two_sample_random_alpha` — `S = {1,…,T}`, `L = log (4T/α)`: false rejection `≤ α`.
  Compare `RandomCount.random_diff_alpha`, which pays `log (2T²/α)`.

Still assumed: the data come from such independent tables (the random-table form of a
time-homogeneous Markov chain), and each table has a common mean `p > 0`.
-/

namespace FiveOrgans.PoissonRandom
open MeasureTheory ProbabilityTheory Finset Real
open FiveOrgans.PoissonTail FiveOrgans.PoissonConf FiveOrgans.RandomCount

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **KL confidence statement, random count.** -/
theorem kl_conf_random {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (hp : 0 < p)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) (N : Ω → ℕ) (hN : ∀ ω, N ω ∈ S) (L : ℝ) :
    μ.real {ω | L ≤ N ω * poisKL ((∑ i ∈ range (N ω), X i ω) / N ω) p}
      ≤ S.card * (2 * exp (-L)) := by
  let bad : ℕ → Set Ω := fun n => {ω | L ≤ n * poisKL ((∑ i ∈ range n, X i ω) / n) p}
  calc _ = μ.real {ω | ω ∈ bad (N ω)} := rfl
    _ ≤ ∑ n ∈ S, μ.real (bad n) := random_index_le bad S N hN
    _ ≤ ∑ _n ∈ S, 2 * exp (-L) := sum_le_sum fun n hn => kl_conf hX hind hr hm (hS n hn) hp L
    _ = S.card * (2 * exp (-L)) := by rw [sum_const, nsmul_eq_mul]

theorem card_Icc_one (T : ℕ) : (Icc 1 T).card = T := by simp

theorem pos_of_Icc {T n : ℕ} (h : n ∈ Icc 1 T) : 0 < n := by have := (mem_Icc.1 h).1; omega

/-- **Calibrated, random count:** `L = log (2T/α)` over a sample of `T` steps. -/
theorem kl_conf_random_alpha {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hr : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[X i] = p) (hp : 0 < p)
    {T : ℕ} (hT : 0 < T) (N : Ω → ℕ) (hN : ∀ ω, N ω ∈ Icc 1 T) {α : ℝ} (hα : 0 < α) :
    μ.real {ω | log (2 * T / α) ≤ N ω * poisKL ((∑ i ∈ range (N ω), X i ω) / N ω) p} ≤ α := by
  have hT' : (0 : ℝ) < T := Nat.cast_pos.2 hT
  refine (kl_conf_random hX hind hr hm hp (Icc 1 T) (fun n hn => pos_of_Icc hn) N hN _).trans_eq ?_
  rw [card_Icc_one, exp_neg_log (by positivity)]; field_simp

/-- **Two-sample KL test, random counts.** -/
theorem kl_two_sample_random {X₁ X₂ : ℕ → Ω → ℝ} (hX₁ : ∀ i, Measurable (X₁ i))
    (hX₂ : ∀ i, Measurable (X₂ i)) (hind₁ : iIndepFun X₁ μ) (hind₂ : iIndepFun X₂ μ)
    (hr₁ : ∀ i ω, X₁ i ω ∈ Set.Icc (0 : ℝ) 1) (hr₂ : ∀ i ω, X₂ i ω ∈ Set.Icc (0 : ℝ) 1)
    {p : ℝ} (hm₁ : ∀ i, μ[X₁ i] = p) (hm₂ : ∀ i, μ[X₂ i] = p) (hp : 0 < p)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) (N₁ N₂ : Ω → ℕ) (hN₁ : ∀ ω, N₁ ω ∈ S)
    (hN₂ : ∀ ω, N₂ ω ∈ S) (L : ℝ) :
    μ.real {ω | ∀ q, 0 < q →
        L ≤ N₁ ω * poisKL ((∑ i ∈ range (N₁ ω), X₁ i ω) / N₁ ω) q ∨
        L ≤ N₂ ω * poisKL ((∑ i ∈ range (N₂ ω), X₂ i ω) / N₂ ω) q}
      ≤ 4 * S.card * exp (-L) := by
  calc _ ≤ μ.real ({ω | L ≤ N₁ ω * poisKL ((∑ i ∈ range (N₁ ω), X₁ i ω) / N₁ ω) p} ∪
            {ω | L ≤ N₂ ω * poisKL ((∑ i ∈ range (N₂ ω), X₂ i ω) / N₂ ω) p}) :=
          measureReal_mono (fun ω hω => by
            simp only [Set.mem_ofPred_eq] at hω; exact hω p hp)
    _ ≤ _ + _ := measureReal_union_le _ _
    _ ≤ S.card * (2 * exp (-L)) + S.card * (2 * exp (-L)) := add_le_add
          (kl_conf_random hX₁ hind₁ hr₁ hm₁ hp S hS N₁ hN₁ L)
          (kl_conf_random hX₂ hind₂ hr₂ hm₂ hp S hS N₂ hN₂ L)
    _ = 4 * S.card * exp (-L) := by ring

/-- **Calibrated two-sample test, random counts:** `L = log (4T/α)`. -/
theorem kl_two_sample_random_alpha {X₁ X₂ : ℕ → Ω → ℝ} (hX₁ : ∀ i, Measurable (X₁ i))
    (hX₂ : ∀ i, Measurable (X₂ i)) (hind₁ : iIndepFun X₁ μ) (hind₂ : iIndepFun X₂ μ)
    (hr₁ : ∀ i ω, X₁ i ω ∈ Set.Icc (0 : ℝ) 1) (hr₂ : ∀ i ω, X₂ i ω ∈ Set.Icc (0 : ℝ) 1)
    {p : ℝ} (hm₁ : ∀ i, μ[X₁ i] = p) (hm₂ : ∀ i, μ[X₂ i] = p) (hp : 0 < p)
    {T : ℕ} (hT : 0 < T) (N₁ N₂ : Ω → ℕ) (hN₁ : ∀ ω, N₁ ω ∈ Icc 1 T) (hN₂ : ∀ ω, N₂ ω ∈ Icc 1 T)
    {α : ℝ} (hα : 0 < α) :
    μ.real {ω | ∀ q, 0 < q →
        log (4 * T / α) ≤ N₁ ω * poisKL ((∑ i ∈ range (N₁ ω), X₁ i ω) / N₁ ω) q ∨
        log (4 * T / α) ≤ N₂ ω * poisKL ((∑ i ∈ range (N₂ ω), X₂ i ω) / N₂ ω) q} ≤ α := by
  have hT' : (0 : ℝ) < T := Nat.cast_pos.2 hT
  refine (kl_two_sample_random hX₁ hX₂ hind₁ hind₂ hr₁ hr₂ hm₁ hm₂ hp (Icc 1 T)
    (fun n hn => pos_of_Icc hn) N₁ N₂ hN₁ hN₂ _).trans_eq ?_
  rw [card_Icc_one, exp_neg_log (by positivity)]; field_simp

end FiveOrgans.PoissonRandom
