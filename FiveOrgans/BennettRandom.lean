import FiveOrgans.BennettDiff
import FiveOrgans.RandomCount

/-!
# Direct difference test with random visit counts

`BennettDiff.bern_diff_two_sample` fixes the counts `N₁, N₂` in advance. On logged data they are
random (how often each state was visited). Sampling model ("stacks"): one independent `[0,1]`
sequence `Z` with common mean `p`; arm 1 observes the prefix `Z 0, Z 2, …, Z (2(N₁−1))` and arm 2
the prefix `Z 1, Z 3, …, Z (2N₂−1)`; the counts `N₁ ω ∈ S₁`, `N₂ ω ∈ S₂` may depend on anything.

* `ew`, `ew_stat`, `ew_sum` — weights `1/n₁` on the first `n₁` even draws, `−1/n₂` on the first
  `n₂` odd draws: the statistic is `p̂₁ − p̂₂` and the weights sum to 0.
* `rej` — the rejection event: for every `q ∈ (0,1)`, `q` lies outside one arm's Bernoulli-KL
  set, or the scaled difference exceeds its `ψ_q` threshold. Scales `su n₁ n₂ q`, `sl n₁ n₂ q`
  are fixed in advance and may depend on the counts.
* `bern_diff_random` — false rejection `≤ |S₁|·2e^{−L} + |S₂|·2e^{−L} + |S₁×S₂|·2e^{−A}`.
* `bern_diff_random_alpha` — counts in `1..T`, `L = log(8T/α)`, `A = log(4T²/α)`: `≤ α`.

The KL part costs only `log T` (one count each); the difference part costs `log T²` because it
depends on both counts. The confidence set for `q` is the intersection of the two arm sets, not
the pooled set used in `BennettDiff`.
-/

namespace FiveOrgans.BennettRandom
open MeasureTheory ProbabilityTheory Finset Real
open FiveOrgans.BernKL FiveOrgans.BennettDiff FiveOrgans.RandomCount FiveOrgans.PoissonRandom

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem sum_range_two_mul (g : ℕ → ℝ) (M : ℕ) :
    ∑ k ∈ range (2 * M), g k = ∑ i ∈ range M, (g (2 * i) + g (2 * i + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

/-- Even/odd difference weights. -/
noncomputable def ew (n₁ n₂ k : ℕ) : ℝ :=
  if k % 2 = 0 then (if k / 2 < n₁ then 1 / n₁ else 0) else (if k / 2 < n₂ then -(1 / n₂) else 0)

theorem ew_stat (n₁ n₂ M : ℕ) (h₁ : n₁ ≤ M) (h₂ : n₂ ≤ M) (f : ℕ → ℝ) :
    ∑ k ∈ range (2 * M), ew n₁ n₂ k * f k
      = (∑ i ∈ range n₁, f (2 * i)) / n₁ - (∑ i ∈ range n₂, f (2 * i + 1)) / n₂ := by
  rw [sum_range_two_mul]
  have e : ∀ i, ew n₁ n₂ (2 * i) * f (2 * i) + ew n₁ n₂ (2 * i + 1) * f (2 * i + 1)
      = (if i < n₁ then f (2 * i) / n₁ else 0) + (if i < n₂ then -(f (2 * i + 1) / n₂) else 0) := by
    intro i
    have h0 : (2 * i) % 2 = 0 := by omega
    have h1 : (2 * i) / 2 = i := by omega
    have h2 : (2 * i + 1) % 2 = 1 := by omega
    have h3 : (2 * i + 1) / 2 = i := by omega
    simp only [ew, h0, h1, h2, h3, one_ne_zero, ↓reduceIte]
    split_ifs <;> ring
  have f1 : (range M).filter (fun i => i < n₁) = range n₁ := by
    ext i; simp only [mem_filter, mem_range]; exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  have f2 : (range M).filter (fun i => i < n₂) = range n₂ := by
    ext i; simp only [mem_filter, mem_range]; exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  rw [sum_congr rfl fun i _ => e i, sum_add_distrib, ← sum_filter, ← sum_filter, f1, f2,
    sum_neg_distrib, sum_div, sum_div]
  ring

theorem ew_sum {n₁ n₂ : ℕ} (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    ∑ k ∈ range (2 * (n₁ + n₂)), ew n₁ n₂ k = 0 := by
  have h := ew_stat n₁ n₂ (n₁ + n₂) (by omega) (by omega) (fun _ => (1 : ℝ))
  simp only [mul_one, sum_const, card_range, nsmul_eq_mul] at h
  rw [h, div_self (Nat.cast_ne_zero.2 h₁.ne'), div_self (Nat.cast_ne_zero.2 h₂.ne'), sub_self]

/-- The difference statistic `p̂₁ − p̂₂` for counts `n₁, n₂`. -/
noncomputable def dstat (Z : ℕ → Ω → ℝ) (n₁ n₂ : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ range n₁, Z (2 * i) ω) / n₁ - (∑ i ∈ range n₂, Z (2 * i + 1) ω) / n₂

/-- The rejection event for counts `n₁, n₂`. -/
def rej (Z : ℕ → Ω → ℝ) (L A : ℝ) (su sl : ℕ → ℕ → ℝ → ℝ) (n₁ n₂ : ℕ) (ω : Ω) : Prop :=
  ∀ q, 0 < q → q < 1 →
    L ≤ n₁ * binKL ((∑ i ∈ range n₁, Z (2 * i) ω) / n₁) q ∨
    L ≤ n₂ * binKL ((∑ i ∈ range n₂, Z (2 * i + 1) ω) / n₂) q ∨
    A + ∑ k ∈ range (2 * (n₁ + n₂)), psi q (su n₁ n₂ q * ew n₁ n₂ k) ≤ su n₁ n₂ q * dstat Z n₁ n₂ ω ∨
    A + ∑ k ∈ range (2 * (n₁ + n₂)), psi q (sl n₁ n₂ q * ew n₁ n₂ k) ≤ sl n₁ n₂ q * dstat Z n₁ n₂ ω

/-- **Direct difference test, random counts.** -/
theorem bern_diff_random {Z : ℕ → Ω → ℝ} (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z μ)
    (hr : ∀ i ω, Z i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ} (hm : ∀ i, μ[Z i] = p) (hp : 0 < p)
    (hp1 : p < 1) (S₁ S₂ : Finset ℕ) (hS₁ : ∀ n ∈ S₁, 0 < n) (hS₂ : ∀ n ∈ S₂, 0 < n)
    (N₁ N₂ : Ω → ℕ) (hN₁ : ∀ ω, N₁ ω ∈ S₁) (hN₂ : ∀ ω, N₂ ω ∈ S₂)
    (su sl : ℕ → ℕ → ℝ → ℝ) (L A : ℝ) :
    μ.real {ω | rej Z L A su sl (N₁ ω) (N₂ ω) ω}
      ≤ S₁.card * (2 * exp (-L)) + S₂.card * (2 * exp (-L)) + (S₁ ×ˢ S₂).card * (2 * exp (-A)) := by
  have hE : iIndepFun (fun i => Z (2 * i)) μ :=
    hind.precomp (g := fun i => 2 * i) (fun a b h => by simp only at h; omega)
  have hO : iIndepFun (fun i => Z (2 * i + 1)) μ :=
    hind.precomp (g := fun i => 2 * i + 1) (fun a b h => by simp only at h; omega)
  let b1 : ℕ → Set Ω := fun n => {ω | L ≤ n * binKL ((∑ i ∈ range n, Z (2 * i) ω) / n) p}
  let b2 : ℕ → Set Ω := fun n => {ω | L ≤ n * binKL ((∑ i ∈ range n, Z (2 * i + 1) ω) / n) p}
  let bD : ℕ × ℕ → Set Ω := fun k =>
    {ω | A + ∑ j ∈ range (2 * (k.1 + k.2)), psi p (su k.1 k.2 p * ew k.1 k.2 j) ≤
        su k.1 k.2 p * ∑ j ∈ range (2 * (k.1 + k.2)), ew k.1 k.2 j * Z j ω} ∪
    {ω | A + ∑ j ∈ range (2 * (k.1 + k.2)), psi p (sl k.1 k.2 p * ew k.1 k.2 j) ≤
        sl k.1 k.2 p * ∑ j ∈ range (2 * (k.1 + k.2)), ew k.1 k.2 j * Z j ω}
  have h1 : ∀ n ∈ S₁, μ.real (b1 n) ≤ 2 * exp (-L) := fun n hn =>
    kl_conf_bern (fun i => hZ _) hE (fun i => hr _) (fun i => hm _) (hS₁ n hn) hp hp1 L
  have h2 : ∀ n ∈ S₂, μ.real (b2 n) ≤ 2 * exp (-L) := fun n hn =>
    kl_conf_bern (fun i => hZ _) hO (fun i => hr _) (fun i => hm _) (hS₂ n hn) hp hp1 L
  have hD : ∀ k ∈ S₁ ×ˢ S₂, μ.real (bD k) ≤ 2 * exp (-A) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := mem_product.1 hk
    have hc := ew_sum (hS₁ _ hk1) (hS₂ _ hk2)
    calc μ.real (bD k) ≤ _ + _ := measureReal_union_le _ _
      _ ≤ exp (-A) + exp (-A) := add_le_add
          (scaled_tail_bern hZ hind hr hm hp hp1 (ew k.1 k.2) _ hc (su k.1 k.2 p) A)
          (scaled_tail_bern hZ hind hr hm hp hp1 (ew k.1 k.2) _ hc (sl k.1 k.2 p) A)
      _ = 2 * exp (-A) := by ring
  calc _ ≤ μ.real (({ω | ω ∈ b1 (N₁ ω)} ∪ {ω | ω ∈ b2 (N₂ ω)}) ∪
            {ω | ω ∈ bD (N₁ ω, N₂ ω)}) := measureReal_mono fun ω hω => by
          simp only [Set.mem_ofPred_eq, rej] at hω
          have es := ew_stat (N₁ ω) (N₂ ω) (N₁ ω + N₂ ω) (by omega) (by omega) (fun k => Z k ω)
          rcases hω p hp hp1 with h | h | h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
          · rw [dstat, ← es] at h; exact Or.inr (Or.inl h)
          · rw [dstat, ← es] at h; exact Or.inr (Or.inr h)
    _ ≤ μ.real (_ ∪ _) + μ.real _ := measureReal_union_le _ _
    _ ≤ (μ.real _ + μ.real _) + μ.real _ := add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ (∑ n ∈ S₁, μ.real (b1 n) + ∑ n ∈ S₂, μ.real (b2 n)) + ∑ k ∈ S₁ ×ˢ S₂, μ.real (bD k) :=
        add_le_add (add_le_add (random_index_le b1 S₁ N₁ hN₁) (random_index_le b2 S₂ N₂ hN₂))
          (random_index_le bD _ (fun ω => (N₁ ω, N₂ ω)) fun ω => mem_product.2 ⟨hN₁ ω, hN₂ ω⟩)
    _ ≤ (∑ _n ∈ S₁, 2 * exp (-L) + ∑ _n ∈ S₂, 2 * exp (-L)) + ∑ _k ∈ S₁ ×ˢ S₂, 2 * exp (-A) :=
        add_le_add (add_le_add (sum_le_sum h1) (sum_le_sum h2)) (sum_le_sum hD)
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

/-- **Calibrated:** counts in `1..T`, `L = log(8T/α)`, `A = log(4T²/α)`. -/
theorem bern_diff_random_alpha {Z : ℕ → Ω → ℝ} (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z μ) (hr : ∀ i ω, Z i ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ}
    (hm : ∀ i, μ[Z i] = p) (hp : 0 < p) (hp1 : p < 1) {T : ℕ} (hT : 0 < T)
    (N₁ N₂ : Ω → ℕ) (hN₁ : ∀ ω, N₁ ω ∈ Icc 1 T) (hN₂ : ∀ ω, N₂ ω ∈ Icc 1 T)
    (su sl : ℕ → ℕ → ℝ → ℝ) {α : ℝ} (hα : 0 < α) :
    μ.real {ω | rej Z (log (8 * T / α)) (log (4 * T ^ 2 / α)) su sl (N₁ ω) (N₂ ω) ω} ≤ α := by
  have hT' : (0 : ℝ) < T := Nat.cast_pos.2 hT
  have hS : ∀ n ∈ Icc 1 T, 0 < n := fun n hn => pos_of_Icc hn
  refine (bern_diff_random hZ hind hr hm hp hp1 _ _ hS hS N₁ N₂ hN₁ hN₂ su sl _ _).trans
    (le_of_eq ?_)
  rw [card_product, card_Icc_one, exp_neg, exp_log (by positivity), exp_neg,
    exp_log (by positivity)]
  push_cast
  field_simp
  ring

end FiveOrgans.BennettRandom
