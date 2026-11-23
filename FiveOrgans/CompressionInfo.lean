import FiveOrgans.Compression
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Predictive compression II: entropy bound, causal states, regret budgets, task relativity

This module continues `Compression` and closes its four open items.

1. **Shannon-entropy lower bound.** Let a distribution `w` on histories be pushed to memory
   states (`push`). Then:
   - Coarsening never raises entropy (`ent_factor_le`).
   - Entropy is at most `log |M|` (`ent_le_log_card`, Gibbs' inequality via `log x ≤ x − 1`).
   - Hence every safe agent with `|M|` states has a *safe action selector* whose action
     entropy is at most its memory entropy, which is at most `log |M|`
     (`safe_entropy_bound`, `memory_ge_decision_entropy`).
   - Read backwards: **memory size ≥ exp(min entropy of a safe selector)**. In bits, divide by
     `log 2`.
   - `entropy_bound_tight`: when every history needs its own action, the bound is attained
     (uniform `n` histories need `log n`).
2. **Causal states and zero-probability transitions.** Updating is only required along
   transitions of positive probability (`PosUpdatable`). Sufficiency still predicts every finite
   future (`seq_sufficient_pos`). The predictive law itself is sufficient and pos-updatable
   (`law_sufficient`, `law_posUpdatable`), and every such statistic refines it
   (`law_minimal`). So the law is the **minimal sufficient predictive state** (the causal state of
   computational mechanics), proved here for finite futures.
3. **Regret becomes a survival budget.** If the per-step hazard is at most `κ ×` regret and
   the compression error at step `i` is `ε_i`, then survival `≥ 1 − 2κ Σ ε_i`
   (`compression_budget`). Summable compression error gives lasting viability
   (`summable_compression_viable`). A constant positive hazard still kills (`const_hazard_dies`).
4. **Useful compression is task-relative** (`useful_compression_task_relative`). The same two
   histories have different predictive laws.
   - Under one task, one memory state is enough. So decision-useful compression can be strictly
     coarser than predictive sufficiency.
   - Under another task, one state is not enough. So the minimum memory is a property of
     histories *and* task, not of history statistics alone.

Scope.
- Finite history sets and finite futures.
- Entropy is of the memory-state distribution of a deterministic memory. It is not the expected
  length of a prefix code; Kraft–McMillan is not formalised.
- The hazard-from-regret link is an assumption on the hazard stream (EMP?).
-/

namespace FiveOrgans.CompressionInfo
open FiveOrgans.Memory FiveOrgans.Compression FiveOrgans.ViabilityStochastic Finset Real

variable {H A M B X : Type*}

/-! ### 1. Entropy of a pushed-forward distribution -/

/-- Shannon entropy (natural log; `0 · log 0 = 0` since `log 0 = 0`). -/
noncomputable def ent [Fintype M] (q : M → ℝ) : ℝ := ∑ m, -(q m * log (q m))

/-- Distribution of `f h` when `h ∼ w`. -/
noncomputable def push [Fintype H] [DecidableEq M] (w : H → ℝ) (f : H → M) (m : M) : ℝ :=
  ∑ h, if f h = m then w h else 0

theorem push_nonneg [Fintype H] [DecidableEq M] {w : H → ℝ} (hw : ∀ h, 0 ≤ w h) (f : H → M)
    (m : M) : 0 ≤ push w f m :=
  sum_nonneg fun h _ => by split_ifs <;> simp [hw h]

theorem push_sum [Fintype H] [Fintype M] [DecidableEq M] (w : H → ℝ) (f : H → M) :
    ∑ m, push w f m = ∑ h, w h := by
  unfold push; rw [sum_comm]; exact sum_congr rfl fun h _ => by simp

theorem le_push [Fintype H] [DecidableEq M] {w : H → ℝ} (hw : ∀ h, 0 ≤ w h) (f : H → M)
    (h : H) : w h ≤ push w f (f h) := by
  unfold push
  have := single_le_sum (f := fun h' => if f h' = f h then w h' else 0)
    (fun h' _ => by split_ifs <;> simp [hw h']) (mem_univ h)
  simpa using this

/-- Entropy as an average over histories. -/
theorem ent_push_eq [Fintype H] [Fintype M] [DecidableEq M] (w : H → ℝ) (f : H → M) :
    ent (push w f) = ∑ h, -(w h * log (push w f (f h))) := by
  unfold ent
  have : ∀ m, -(push w f m * log (push w f m)) =
      ∑ h, if f h = m then -(w h * log (push w f (f h))) else 0 := by
    intro m
    conv_lhs => rw [push, sum_mul, ← sum_neg_distrib]
    refine sum_congr rfl fun h _ => ?_
    split_ifs with e
    · rw [e]; rfl
    · simp
  rw [sum_congr rfl fun m _ => this m, sum_comm]
  exact sum_congr rfl fun h _ => by simp

/-- **Coarsening never raises entropy.** -/
theorem ent_factor_le [Fintype H] [Fintype M] [Fintype B] [DecidableEq M] [DecidableEq B]
    {w : H → ℝ} (hw : ∀ h, 0 ≤ w h) (F : M → B) (k : H → M) :
    ent (push w (F ∘ k)) ≤ ent (push w k) := by
  rw [ent_push_eq, ent_push_eq]
  refine sum_le_sum fun h _ => ?_
  rcases (hw h).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  have hq : 0 < push w k (k h) := hpos.trans_le (le_push hw k h)
  have hQ : push w k (k h) ≤ push w (F ∘ k) ((F ∘ k) h) := by
    unfold push
    refine sum_le_sum fun h' _ => ?_
    by_cases e : k h' = k h
    · simp [e]
    · simp only [e, ↓reduceIte]; split_ifs <;> simp [hw h']
  have := log_le_log hq hQ
  nlinarith

/-- **Gibbs:** entropy is at most `log |M|`. -/
theorem ent_le_log_card [Fintype M] {q : M → ℝ} (hq : ∀ m, 0 ≤ q m) (h1 : ∑ m, q m = 1) :
    ent q ≤ log (Fintype.card M) := by
  have hn : (0 : ℝ) < Fintype.card M := by
    have : 0 < Fintype.card M := by
      rcases isEmpty_or_nonempty M with hM | hM
      · simp at h1
      · exact Fintype.card_pos
    exact_mod_cast this
  set n : ℝ := (Fintype.card M : ℝ)
  have term : ∀ m, -(q m * log (q m)) - q m * log n ≤ 1 / n - q m := by
    intro m
    rcases (hq m).eq_or_lt with h0 | hp
    · rw [← h0]; simp; positivity
    have hx : 0 < 1 / (q m * n) := by positivity
    have hl := log_le_sub_one_of_pos hx
    rw [one_div, log_inv, log_mul hp.ne' hn.ne'] at hl
    have hmul := mul_le_mul_of_nonneg_left hl hp.le
    have : q m * ((q m * n)⁻¹ - 1) = 1 / n - q m := by field_simp
    nlinarith
  have hs := sum_le_sum fun m (_ : m ∈ univ) => term m
  rw [sum_sub_distrib, sum_sub_distrib, ← sum_mul, h1, sum_const, card_univ, nsmul_eq_mul] at hs
  unfold ent
  have : (Fintype.card M : ℝ) * (1 / n) = 1 := by
    rw [show (Fintype.card M : ℝ) = n from rfl]; field_simp
  linarith

/-- **Entropy lower bound for a safe agent.** Its action map is a safe selector whose entropy is
`≤` the memory entropy `≤ log |M|`. -/
theorem safe_entropy_bound [Fintype H] [Fintype M] [DecidableEq M] [Fintype A] [DecidableEq A]
    {safe : H → A → Prop} {mem : H → M} {π : M → A} (hs : SafeAgent safe mem π)
    {w : H → ℝ} (hw : ∀ h, 0 ≤ w h) (hw1 : ∑ h, w h = 1) :
    (∀ h, safe h ((π ∘ mem) h)) ∧ ent (push w (π ∘ mem)) ≤ ent (push w mem) ∧
      ent (push w mem) ≤ log (Fintype.card M) :=
  ⟨hs, ent_factor_le hw π mem,
    ent_le_log_card (push_nonneg hw mem) (by rw [push_sum, hw1])⟩

/-- **Memory size ≥ decision entropy.** Any safe agent with memory type `M` gives a safe selector
`s` with `ent(s) ≤ log |M|`, so `|M| ≥ exp(min over safe selectors of ent(s))`. -/
theorem memory_ge_decision_entropy [Fintype H] [Fintype M] [DecidableEq M] [Fintype A]
    [DecidableEq A] {safe : H → A → Prop} {mem : H → M} {π : M → A}
    (hs : SafeAgent safe mem π) {w : H → ℝ} (hw : ∀ h, 0 ≤ w h) (hw1 : ∑ h, w h = 1) :
    ∃ s : H → A, (∀ h, safe h (s h)) ∧ ent (push w s) ≤ log (Fintype.card M) := by
  obtain ⟨h1, h2, h3⟩ := safe_entropy_bound hs hw hw1
  exact ⟨_, h1, h2.trans h3⟩

/-- Tightness: if the only safe action after `h` is `h` itself, the action entropy of every safe
selector equals the entropy of `w`, which for uniform `w` on `n` histories is `log n`. -/
theorem entropy_bound_tight (n : ℕ) (hn : 0 < n) (s : Fin n → Fin n) (hs : ∀ h, s h = h) :
    ent (push (fun _ : Fin n => (1 : ℝ) / n) s) = log n := by
  have hsid : s = id := funext hs
  subst hsid
  have : push (fun _ : Fin n => (1 : ℝ) / n) id = fun _ => (1 : ℝ) / n := by
    funext m; unfold push; simp
  rw [this]; unfold ent
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, one_div, log_inv]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-! ### 2. Causal states and zero-probability transitions -/

/-- Updating required only along transitions of positive probability. -/
def PosUpdatable {S : Type*} (P : H → X → ℝ) (push : H → X → H) (σ : H → S) : Prop :=
  ∀ h₁ h₂, σ h₁ = σ h₂ → ∀ x, P h₁ x ≠ 0 → σ (push h₁ x) = σ (push h₂ x)

theorem seq_sufficient_pos {S : Type*} {P : H → X → ℝ} {push : H → X → H} {σ : H → S}
    (hs : Sufficient P σ) (hu : PosUpdatable P push σ) :
    ∀ xs h₁ h₂, σ h₁ = σ h₂ → seqProb P push h₁ xs = seqProb P push h₂ xs := by
  intro xs
  induction xs with
  | nil => intro _ _ _; rfl
  | cons x xs ih =>
    intro h₁ h₂ e
    simp only [seqProb]
    have hP := hs h₁ h₂ e
    by_cases h0 : P h₁ x = 0
    · rw [← hP, h0, zero_mul, zero_mul]
    · rw [← hP, ih _ _ (hu h₁ h₂ e x h0)]

/-- The predictive law is sufficient. -/
theorem law_sufficient (P : H → X → ℝ) (push : H → X → H) :
    Sufficient P (seqProb P push) := by
  intro h₁ h₂ e
  funext x
  have := congrFun e [x]
  simpa [seqProb] using this

/-- The predictive law is updatable along positive-probability transitions. -/
theorem law_posUpdatable (P : H → X → ℝ) (push : H → X → H) :
    PosUpdatable P push (seqProb P push) := by
  intro h₁ h₂ e x hx
  funext xs
  have h := congrFun e (x :: xs)
  have hP : P h₁ x = P h₂ x := congrFun (law_sufficient P push h₁ h₂ e) x
  simp only [seqProb] at h
  rw [← hP] at h
  exact mul_left_cancel₀ hx h

/-- **Minimality of the causal state.** Every sufficient, pos-updatable statistic refines the
predictive law. -/
theorem law_minimal {S : Type*} {P : H → X → ℝ} {push : H → X → H} {σ : H → S}
    (hs : Sufficient P σ) (hu : PosUpdatable P push σ) {h₁ h₂ : H} (e : σ h₁ = σ h₂) :
    seqProb P push h₁ = seqProb P push h₂ :=
  funext fun xs => seq_sufficient_pos hs hu xs h₁ h₂ e

/-! ### 3. Regret as a survival budget -/

/-- **Compression error budget.** Per-step hazard `≤ κ ·` regret and compression error `ε_i` at
step `i` give survival `≥ 1 − 2κ Σ ε_i`. -/
theorem compression_budget {ℓ : H → A → ℝ} {mem : ℕ → H → M} {rep : ℕ → M → H}
    {π : ℕ → M → A} {ε : ℕ → ℝ} (hopt : ∀ i m a, ℓ (rep i m) (π i m) ≤ ℓ (rep i m) a)
    (hclose : ∀ i h, Close ℓ (ε i) h (rep i (mem i h))) (e : ℕ → H) (astar : H → A)
    {κ : ℝ} (hκ : 0 ≤ κ) {η : ℕ → ℝ} (hη : ∀ i, 0 ≤ η i ∧ η i ≤ 1)
    (hreg : ∀ i, η i ≤ κ * (ℓ (e i) (π i (mem i (e i))) - ℓ (e i) (astar (e i)))) (n : ℕ) :
    1 - 2 * κ * ∑ i ∈ range n, ε i ≤ surv η n := by
  have hb : ∑ i ∈ range n, η i ≤ 2 * κ * ∑ i ∈ range n, ε i := by
    rw [mul_sum]
    refine sum_le_sum fun i _ => ?_
    have := regret_le (hopt i) (hclose i) (e i) (astar (e i))
    have := mul_le_mul_of_nonneg_left (show ℓ (e i) (π i (mem i (e i))) -
      ℓ (e i) (astar (e i)) ≤ 2 * ε i by linarith) hκ
    linarith [hreg i]
  linarith [surv_ge η hη n]

/-- **Summable compression error ⇒ lasting viability.** -/
theorem summable_compression_viable {ℓ : H → A → ℝ} {mem : ℕ → H → M} {rep : ℕ → M → H}
    {π : ℕ → M → A} {ε : ℕ → ℝ} (hopt : ∀ i m a, ℓ (rep i m) (π i m) ≤ ℓ (rep i m) a)
    (hclose : ∀ i h, Close ℓ (ε i) h (rep i (mem i h))) (e : ℕ → H) (astar : H → A)
    {κ : ℝ} (hκ : 0 ≤ κ) {η : ℕ → ℝ} (hη : ∀ i, 0 ≤ η i ∧ η i ≤ 1)
    (hreg : ∀ i, η i ≤ κ * (ℓ (e i) (π i (mem i (e i))) - ℓ (e i) (astar (e i))))
    {E : ℝ} (hE : ∀ n, ∑ i ∈ range n, ε i ≤ E) (n : ℕ) :
    1 - 2 * κ * E ≤ surv η n := by
  have := compression_budget hopt hclose e astar hκ hη hreg n
  have := mul_le_mul_of_nonneg_left (hE n) (by positivity : (0:ℝ) ≤ 2 * κ)
  linarith

/-! ### 4. Useful compression is task-relative -/

/-- Two histories with different predictive laws. Under the trivial task one memory state is
safe, so decision-useful compression is strictly coarser than predictive sufficiency. Under
the "name the history" task, one state is not safe. -/
theorem useful_compression_task_relative :
    let P : Bool → Bool → ℝ := fun h x => if x = h then 1 else 0
    let push : Bool → Bool → Bool := fun h _ => h
    seqProb P push true ≠ seqProb P push false ∧
    (∃ (mem : Bool → Fin 1) (π : Fin 1 → Bool), SafeAgent (fun _ _ => True) mem π) ∧
    ¬ ∃ (mem : Bool → Fin 1) (π : Fin 1 → Bool), SafeAgent (fun h a => a = h) mem π := by
  intro P push
  refine ⟨fun e => ?_, ⟨fun _ => 0, fun _ => true, fun _ => trivial⟩, ?_⟩
  · have := congrFun e [true]
    simp [seqProb, P] at this
  · rintro ⟨mem, π, hs⟩
    have h1 := hs true
    have h2 := hs false
    rw [Subsingleton.elim (mem false) (mem true)] at h2
    rw [h1] at h2
    exact Bool.noConfusion h2

end FiveOrgans.CompressionInfo
