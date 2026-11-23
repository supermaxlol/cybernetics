import FiveOrgans.MemoryViability

/-!
# Predictive compression: what a memory must keep, and what forgetting costs

`Memory` proves that a safe agent separates incompatible histories, and that `k` pairwise
incompatible histories need `k` memory states. This module turns that into a theory of
*decision-relevant compression*. It adds to `Memory`; it does not change it.

Setting as in `Memory`: histories `H`, actions `A`, memory map `mem : H → M`, policy `π : M → A`.

1. **History equivalence.** `DecEquiv safe h₁ h₂` (same safe actions) is an equivalence
   (`decEquiv_equivalence`). Storing only the safe-action set loses nothing
   (`safeSet_adequate`), and so does any memory that merges only equivalent histories
   (`factor_adequate`).
2. **Exact minimum memory.** A memory with `k` states admits a safe policy iff `k` actions cover
   every history (`adequate_fin_iff`). So the minimum memory size is the *action cover number*,
   not the pairwise-incompatibility count of `Memory.card_le_of_pairwise`. Adequacy transports
   along any injection of memory types (`adequate_transport`). `pairwise_bound_loose`: three
   histories, every two compatible (pairwise bound 1), yet no 1-state memory is safe and
   2 states are.
3. **Bits.** `bits_iff`: `b` bits suffice iff some `2^b` actions cover every history.
   This is a counting (Hartley) bound. It is not a Shannon-entropy bound; see Scope.
4. **Sufficient predictive states.** With a next-observation kernel `P : H → X → ℝ` and an update
   `push`, a statistic `σ` that is one-step sufficient and updatable predicts every finite future
   (`seq_sufficient`); the full predictive law factors through it (`law_factors`). Hence the
   predictive law is the coarsest such statistic, and the number of distinct predictive laws on
   any finite set of histories is a lower bound on the number of states (`card_laws_le`).
5. **Approximate compression and regret.** If every history is `ε`-close in loss to the
   representative of its memory state, acting optimally for the representative costs at most `2ε`
   regret per history (`regret_le`) and in expectation (`expected_regret_le`). Conversely,
   merging two histories whose actions have summed regret at least `g` forces regret `≥ g/2` on
   one of them, for every policy (`merge_regret_ge`).
6. **Forgetting and viability.** With safety as a loss threshold, `ε`-close compression keeps
   survival at 1 in every environment when the safe margin is at least `2ε`
   (`approx_compression_survives`). A forgetting map `f` on memory states is harmless iff each of
   its fibres shares a safe action (`forget_safe_iff`). If it merges two incompatible histories,
   some environment drives survival below any level (`forget_kills`).

Scope. Pure combinatorics and finite sums. "Information-theoretic" here means counting states;
a Shannon-entropy version (expected code length under a history distribution) is not formalised.
The predictive part handles one-step sufficiency plus deterministic updating. Conditioning on
zero-probability transitions (where the causal-state construction needs care) is not treated.
Nothing here is a claim about real memory systems.
-/

namespace FiveOrgans.Compression
open FiveOrgans.Memory FiveOrgans.ViabilityStochastic FiveOrgans.MemoryViability Finset

variable {H A M M' X S : Type*}

/-! ### 1. Decision-relevant history equivalence -/

/-- Two histories are decision-equivalent if they have exactly the same safe actions. -/
def DecEquiv (safe : H → A → Prop) (h₁ h₂ : H) : Prop := ∀ a, safe h₁ a ↔ safe h₂ a

theorem decEquiv_equivalence (safe : H → A → Prop) : Equivalence (DecEquiv safe) :=
  ⟨fun _ _ => Iff.rfl, fun h a => (h a).symm, fun h g a => (h a).trans (g a)⟩

/-- Any memory that merges only decision-equivalent histories is adequate, provided every
history has a safe action. -/
theorem factor_adequate [Nonempty A] (safe : H → A → Prop) (hex : ∀ h, ∃ a, safe h a)
    (mem : H → M) (hmem : ∀ h₁ h₂, mem h₁ = mem h₂ → DecEquiv safe h₁ h₂) :
    ∃ π : M → A, SafeAgent safe mem π := by
  classical
  refine (adequate_iff safe mem).2 fun m => ?_
  by_cases hm : ∃ h, mem h = m
  · obtain ⟨h₀, rfl⟩ := hm
    obtain ⟨a, ha⟩ := hex h₀
    exact ⟨a, fun h hh => (hmem h h₀ hh a).2 ha⟩
  · exact ⟨Classical.arbitrary A, fun h hh => absurd ⟨h, hh⟩ hm⟩

/-- Storing the safe-action set itself is enough. -/
theorem safeSet_adequate [Nonempty A] (safe : H → A → Prop) (hex : ∀ h, ∃ a, safe h a) :
    ∃ π : (A → Prop) → A, SafeAgent safe (fun h => safe h) π :=
  factor_adequate safe hex _ fun h₁ h₂ e a => by rw [e]

/-! ### 2. Exact minimum memory: the action cover number -/

/-- A set of actions covers the histories if every history has a safe action in it. -/
def Covers (safe : H → A → Prop) (B : Finset A) : Prop := ∀ h, ∃ a ∈ B, safe h a

/-- Adequacy is preserved by an injective relabelling of memory states. -/
theorem adequate_transport [Nonempty A] {safe : H → A → Prop} {mem : H → M} {π : M → A}
    (hs : SafeAgent safe mem π) (f : M → M') (hf : Function.Injective f) :
    SafeAgent safe (f ∘ mem) (Function.extend f π fun _ => Classical.arbitrary A) := by
  intro h
  simp only [Function.comp_apply, hf.extend_apply]
  exact hs h

/-- A safe agent's actions cover the histories. -/
theorem covers_of_safe [DecidableEq A] [Fintype M] {safe : H → A → Prop} {mem : H → M}
    {π : M → A} (hs : SafeAgent safe mem π) :
    Covers safe (univ.image π) ∧ (univ.image π).card ≤ Fintype.card M :=
  ⟨fun h => ⟨π (mem h), mem_image_of_mem _ (mem_univ _), hs h⟩, card_image_le⟩

/-- A cover gives a safe agent whose memory states are the cover's actions. -/
theorem safe_of_covers {safe : H → A → Prop} {B : Finset A} (hB : Covers safe B) :
    ∃ mem : H → B, SafeAgent safe mem Subtype.val := by
  choose a ha hs using hB
  exact ⟨fun h => ⟨a h, ha h⟩, hs⟩

/-- **Exact minimum memory.** `k` memory states admit a safe policy iff `k` actions cover every
history. -/
theorem adequate_fin_iff [Nonempty A] (safe : H → A → Prop) (k : ℕ) :
    (∃ (mem : H → Fin k) (π : Fin k → A), SafeAgent safe mem π) ↔
      ∃ B : Finset A, B.card ≤ k ∧ Covers safe B := by
  classical
  constructor
  · rintro ⟨mem, π, hs⟩
    obtain ⟨hc, hk⟩ := covers_of_safe hs
    exact ⟨_, by simpa using hk, hc⟩
  · rintro ⟨B, hk, hB⟩
    obtain ⟨mem, hs⟩ := safe_of_covers hB
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
      (α := B) (β := Fin k) (by simpa using hk)
    exact ⟨_, _, adequate_transport hs f f.injective⟩

/-- **Bits.** `b` bits of memory suffice iff some `2^b` actions cover every history. -/
theorem bits_iff [Nonempty A] (safe : H → A → Prop) (b : ℕ) :
    (∃ (mem : H → Fin (2 ^ b)) (π : Fin (2 ^ b) → A), SafeAgent safe mem π) ↔
      ∃ B : Finset A, B.card ≤ 2 ^ b ∧ Covers safe B :=
  adequate_fin_iff safe (2 ^ b)

/-- **The pairwise bound can be loose.** Three histories, action `a` unsafe only after history
`a`: every two histories share a safe action (so `card_le_of_pairwise` gives only 1), yet no
1-state memory is safe, and 2 states are. -/
theorem pairwise_bound_loose :
    (∀ x y : Fin 3, ¬ Incompatible (fun h a : Fin 3 => a ≠ h) x y) ∧
    (¬ ∃ (mem : Fin 3 → Fin 1) (π : Fin 1 → Fin 3), SafeAgent (fun h a => a ≠ h) mem π) ∧
    (∃ (mem : Fin 3 → Fin 2) (π : Fin 2 → Fin 3), SafeAgent (fun h a => a ≠ h) mem π) := by
  refine ⟨fun x y hinc => ?_, ?_, ?_⟩
  · -- some action differs from both x and y
    have : ∃ a : Fin 3, a ≠ x ∧ a ≠ y := by clear hinc; revert x y; decide
    obtain ⟨a, hx, hy⟩ := this
    exact hinc a hx hy
  · rintro ⟨mem, π, hs⟩
    have h := hs (π 0)
    rw [Subsingleton.elim (mem (π 0)) 0] at h
    exact h rfl
  · refine ⟨fun h => if h = 0 then 0 else 1, ![1, 0], ?_⟩
    intro h; revert h; decide

/-! ### 3. Sufficient predictive states -/

/-- Probability of a finite future sequence from history `h`. -/
def seqProb (P : H → X → ℝ) (push : H → X → H) : H → List X → ℝ
  | _, [] => 1
  | h, x :: xs => P h x * seqProb P push (push h x) xs

/-- `σ` determines the next-observation law. -/
def Sufficient (P : H → X → ℝ) (σ : H → S) : Prop := ∀ h₁ h₂, σ h₁ = σ h₂ → P h₁ = P h₂

/-- `σ` can be updated from its own value and the new observation. -/
def Updatable (push : H → X → H) (σ : H → S) : Prop :=
  ∀ h₁ h₂, σ h₁ = σ h₂ → ∀ x, σ (push h₁ x) = σ (push h₂ x)

/-- **A sufficient, updatable statistic predicts every finite future.** -/
theorem seq_sufficient {P : H → X → ℝ} {push : H → X → H} {σ : H → S}
    (hs : Sufficient P σ) (hu : Updatable push σ) :
    ∀ xs h₁ h₂, σ h₁ = σ h₂ → seqProb P push h₁ xs = seqProb P push h₂ xs := by
  intro xs
  induction xs with
  | nil => intro _ _ _; rfl
  | cons x xs ih =>
    intro h₁ h₂ e
    simp only [seqProb]
    rw [hs h₁ h₂ e, ih _ _ (hu h₁ h₂ e x)]

/-- The whole predictive law factors through any sufficient updatable statistic, so the law is
the coarsest such statistic. -/
theorem law_factors {P : H → X → ℝ} {push : H → X → H} {σ : H → S}
    (hs : Sufficient P σ) (hu : Updatable push σ) :
    ∃ F : S → List X → ℝ, ∀ h, seqProb P push h = F (σ h) := by
  classical
  refine ⟨fun s => if hs' : ∃ h, σ h = s then seqProb P push hs'.choose else fun _ => 0,
    fun h => ?_⟩
  have hex : ∃ h', σ h' = σ h := ⟨h, rfl⟩
  dsimp only
  simp only [hex, ↓reduceDIte]
  funext xs
  exact seq_sufficient hs hu xs _ _ hex.choose_spec.symm

/-- **Lower bound.** A sufficient updatable statistic with `k` values needs `k` at least the
number of distinct predictive laws on any finite set of histories. -/
theorem card_laws_le {P : H → X → ℝ} {push : H → X → H} {k : ℕ} {σ : H → Fin k}
    (hs : Sufficient P σ) (hu : Updatable push σ) (T : Finset H)
    [DecidableEq (List X → ℝ)] : (T.image (seqProb P push)).card ≤ k := by
  classical
  obtain ⟨F, hF⟩ := law_factors hs hu
  have : T.image (seqProb P push) = (T.image σ).image F := by
    rw [image_image]; exact image_congr fun h _ => hF h
  rw [this]
  exact card_image_le.trans ((card_le_univ _).trans (by simp))

/-! ### 4. Approximate compression and decision regret -/

/-- Two histories are `ε`-close in loss. -/
def Close (ℓ : H → A → ℝ) (ε : ℝ) (h₁ h₂ : H) : Prop := ∀ a, |ℓ h₁ a - ℓ h₂ a| ≤ ε

/-- **Regret of approximate compression.** Every history `ε`-close to its state's representative,
policy optimal for the representative ⇒ regret `≤ 2ε` after every history. -/
theorem regret_le {ℓ : H → A → ℝ} {ε : ℝ} {mem : H → M} {rep : M → H} {π : M → A}
    (hopt : ∀ m a, ℓ (rep m) (π m) ≤ ℓ (rep m) a) (hclose : ∀ h, Close ℓ ε h (rep (mem h)))
    (h : H) (a : A) : ℓ h (π (mem h)) ≤ ℓ h a + 2 * ε := by
  have h1 := (abs_le.1 (hclose h (π (mem h)))).2
  have h2 := (abs_le.1 (hclose h a)).1
  have h3 := hopt (mem h) a
  linarith

/-- Expected version, for any comparison policy `a⋆` and any weights summing to 1. -/
theorem expected_regret_le [Fintype H] {ℓ : H → A → ℝ} {ε : ℝ} {mem : H → M} {rep : M → H}
    {π : M → A} (hopt : ∀ m a, ℓ (rep m) (π m) ≤ ℓ (rep m) a)
    (hclose : ∀ h, Close ℓ ε h (rep (mem h))) {w : H → ℝ} (hw : ∀ h, 0 ≤ w h)
    (hw1 : ∑ h, w h = 1) (astar : H → A) :
    ∑ h, w h * ℓ h (π (mem h)) ≤ ∑ h, w h * ℓ h (astar h) + 2 * ε := by
  calc ∑ h, w h * ℓ h (π (mem h)) ≤ ∑ h, w h * (ℓ h (astar h) + 2 * ε) :=
        sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (regret_le hopt hclose h _) (hw h)
    _ = ∑ h, w h * ℓ h (astar h) + 2 * ε := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, hw1, one_mul]

/-- **Merging costs regret.** If every action has summed regret at least `g` across `h₁, h₂`,
any memory that merges them has regret `≥ g/2` on one of them, whatever the policy. -/
theorem merge_regret_ge {ℓ : H → A → ℝ} {mem : H → M} {h₁ h₂ : H} (e : mem h₁ = mem h₂)
    {v₁ v₂ g : ℝ} (hgap : ∀ a, g ≤ (ℓ h₁ a - v₁) + (ℓ h₂ a - v₂)) (π : M → A) :
    g / 2 ≤ max (ℓ h₁ (π (mem h₁)) - v₁) (ℓ h₂ (π (mem h₂)) - v₂) := by
  rw [← e]
  have := hgap (π (mem h₁))
  have := le_max_left (ℓ h₁ (π (mem h₁)) - v₁) (ℓ h₂ (π (mem h₁)) - v₂)
  have := le_max_right (ℓ h₁ (π (mem h₁)) - v₁) (ℓ h₂ (π (mem h₁)) - v₂)
  linarith

/-! ### 5. Forgetting and viability -/

/-- **Approximate compression with margin keeps survival at 1.** Safety = loss `≤ θ`. If every
history has an action with loss `≤ θ − 2ε`, an `ε`-close compression acting optimally for its
representatives is safe, so survival is 1 in every environment. -/
theorem approx_compression_survives {ℓ : H → A → ℝ} {ε θ : ℝ} {mem : H → M} {rep : M → H}
    {π : M → A} (hopt : ∀ m a, ℓ (rep m) (π m) ≤ ℓ (rep m) a)
    (hclose : ∀ h, Close ℓ ε h (rep (mem h))) (hmargin : ∀ h, ∃ a, ℓ h a ≤ θ - 2 * ε)
    (c : ℝ) (e : ℕ → H) (n : ℕ) :
    surv (hz c (fun h a => ℓ h a ≤ θ) mem π e) n = 1 := by
  refine memory_survives (fun h => ?_) c e n
  obtain ⟨a, ha⟩ := hmargin h
  have := regret_le hopt hclose h a
  show ℓ h (π (mem h)) ≤ θ
  linarith

/-- **When forgetting is harmless.** Coarsening memory by `f` keeps some safe policy iff every
`f`-fibre's histories share a safe action. -/
theorem forget_safe_iff (safe : H → A → Prop) (mem : H → M) (f : M → M') :
    (∃ π : M' → A, SafeAgent safe (f ∘ mem) π) ↔
      ∀ m', ∃ a, ∀ h, f (mem h) = m' → safe h a :=
  adequate_iff safe (f ∘ mem)

/-- **When forgetting kills.** If `f` merges the memory states of two incompatible histories,
then for every policy on the coarse memory some environment drawn from those two histories drives
survival below `1 − ε`. -/
theorem forget_kills {safe : H → A → Prop} {mem : H → M} (f : M → M') {h₁ h₂ : H}
    (hmerge : f (mem h₁) = f (mem h₂)) (hinc : Incompatible safe h₁ h₂) (π : M' → A)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {ε : ℝ} (hε : ε < 1) :
    ∃ e : ℕ → H, (∀ i, e i = h₁ ∨ e i = h₂) ∧
      ∃ n, surv (hz c safe (f ∘ mem) π e) n < 1 - ε :=
  memoryless_dies (observe := f ∘ mem) π hmerge hinc hc0 hc1 hε

end FiveOrgans.Compression
