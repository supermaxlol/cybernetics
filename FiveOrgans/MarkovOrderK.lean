import FiveOrgans.MarkovOrder

/-!
# Markov order k as lumpability (all orders)

`MarkovOrder` handles order 2 → 1 through pairs. Here the same fact is proved once for abstract
histories, then instantiated for windows of any length.

Abstract setting: long histories `H`, short histories `S`, a symbol alphabet `X`, a forgetting map
`π : H → S`, and shift maps `push : H → X → H`, `pushS : S → X → S` (append the new symbol, drop
the oldest) with `π (push h c) = pushS (π h) c`. A kernel `P : H → X → ℝ` (next symbol given the
long history) induces the chain `liftH P` on `H`.

* `liftH_blk` — the block row of `liftH P` from `h` into `π⁻¹{s'}` is `Σ_c [pushS (π h) c = s'] P h c`.
* `order_iff_lumpable` — if `pushS s` is injective, **the extra history is irrelevant
  (`P h c = R (π h) c`) iff `liftH P` is lumpable onto `liftH R` through `π`.**
* `sv_order` — survival transfer under reduced order. `order_check_refutes` — the order check is
  `split_refutes_lumpable` on the long-history chain.
* Windows: `win m = Fin (m+1) → X`, `shift w c = Fin.snoc (Fin.tail w) c`, forgetting = `Fin.tail`
  (drop the oldest). `window_order_iff`: an order-`(m+2)` chain is of order `m+1` iff its window
  chain is lumpable onto the order-`(m+1)` window chain. This covers every order.

Reading: "find a Markov micro level" means find `m` such that the window chain of length `m+1`
passes; the lumpability tests in `CrossScaleTest`/`DiffContrast` are then also order tests, valid
under the null "order ≤ m+1". Nothing here says any real system has finite order.
-/

namespace FiveOrgans.MarkovOrderK
open Finset Classical FiveOrgans.CrossScaleMarkov FiveOrgans.CrossScaleTest

variable {H S X : Type*} [Fintype H] [Fintype S] [Fintype X]

/-- Chain on histories: from `h`, append symbol `c` with probability `P h c`. -/
noncomputable def liftH (push : H → X → H) (P : H → X → ℝ) (h h' : H) : ℝ :=
  ∑ c, if push h c = h' then P h c else 0

omit [Fintype S] in
theorem liftH_blk (π : H → S) (push : H → X → H) (pushS : S → X → S)
    (hc : ∀ h c, π (push h c) = pushS (π h) c) (P : H → X → ℝ) (h : H) (s' : S) :
    ∑ h' ∈ univ.filter (fun h' => π h' = s'), liftH push P h h'
      = ∑ c, if pushS (π h) c = s' then P h c else 0 := by
  unfold liftH
  rw [Finset.sum_comm]
  refine sum_congr rfl fun c _ => ?_
  rw [Finset.sum_ite_eq]
  simp [hc]

omit [Fintype S] in
/-- **Order reduction as lumpability.** -/
theorem order_iff_lumpable (π : H → S) (push : H → X → H) (pushS : S → X → S)
    (hc : ∀ h c, π (push h c) = pushS (π h) c) (hinj : ∀ s, Function.Injective (pushS s))
    (P : H → X → ℝ) (R : S → X → ℝ) :
    Lumpable π (liftH push P) (liftH pushS R) ↔ ∀ h c, P h c = R (π h) c := by
  have key : ∀ (f : X → ℝ) (s : S) (c : X),
      (∑ c', if pushS s c' = pushS s c then f c' else 0) = f c := by
    intro f s c
    rw [Finset.sum_eq_single c]
    · simp
    · intro c' _ hne; exact ite_eq_right_iff.2 fun h => absurd (hinj s h) hne
    · simp
  constructor
  · intro hL h c
    have h1 := hL h (pushS (π h) c)
    rw [liftH_blk π push pushS hc] at h1
    unfold liftH at h1
    rwa [key (P h), key (R (π h))] at h1
  · intro hPR h s'
    rw [liftH_blk π push pushS hc]
    unfold liftH
    exact sum_congr rfl fun c _ => by rw [hPR]

/-- **Survival transfer under reduced order.** -/
theorem sv_order {π : H → S} {push : H → X → H} {pushS : S → X → S}
    (hc : ∀ h c, π (push h c) = pushS (π h) c) (hinj : ∀ s, Function.Injective (pushS s))
    {P : H → X → ℝ} {R : S → X → ℝ} (hPR : ∀ h c, P h c = R (π h) c)
    (K : Set S) (n : ℕ) (h : H) :
    sv (liftH push P) (π ⁻¹' K) n h = sv (liftH pushS R) K n (π h) :=
  sv_lump ((order_iff_lumpable π push pushS hc hinj P R).2 hPR) K n h

/-- **The order check is a lumpability test on the long-history chain.** -/
theorem order_check_refutes {π : H → S} {push : H → X → H} {pushS : S → X → S}
    (hc : ∀ h c, π (push h c) = pushS (π h) c) (hinj : ∀ s, Function.Injective (pushS s))
    {P : H → X → ℝ} {Ph : H → H → ℝ} {δ : ℝ} {h₁ h₂ : H} (hφ : π h₁ = π h₂)
    (e1 : rowErr (liftH push P) Ph h₁ ≤ δ) (e2 : rowErr (liftH push P) Ph h₂ ≤ δ)
    (hgap : 2 * δ < ∑ s', |blk π Ph h₁ s' - blk π Ph h₂ s'|) :
    ¬ ∃ R : S → X → ℝ, ∀ h c, P h c = R (π h) c := by
  rintro ⟨R, hR⟩
  exact split_refutes_lumpable hφ e1 e2 hgap
    ⟨_, (order_iff_lumpable π push pushS hc hinj P R).2 hR⟩

/-! ### Windows: every order -/

/-- Window of the last `m + 1` symbols, oldest at index `0`. -/
abbrev win (X : Type*) (m : ℕ) := Fin (m + 1) → X

/-- Append `c`, drop the oldest. -/
def shift {m : ℕ} (w : win X m) (c : X) : win X m := Fin.snoc (Fin.tail w) c

omit [Fintype X] in
theorem shift_inj {m : ℕ} (w : win X m) : Function.Injective (shift w) := by
  intro c c' h
  have := congrFun h (Fin.last m)
  simpa [shift] using this

omit [Fintype X] in
theorem tail_shift {m : ℕ} (w : win X (m + 1)) (c : X) :
    Fin.tail (shift w c) = shift (Fin.tail w) c := by
  funext i
  simp only [shift, Fin.tail]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl

/-- **Every order.** An order-`(m+2)` chain (next symbol given the last `m+2`) reduces to order
`m+1` iff its window chain is lumpable onto the order-`(m+1)` window chain via `Fin.tail`. -/
theorem window_order_iff {m : ℕ} (P : win X (m + 1) → X → ℝ) (R : win X m → X → ℝ) :
    Lumpable Fin.tail (liftH shift P) (liftH shift R) ↔ ∀ w c, P w c = R (Fin.tail w) c :=
  order_iff_lumpable Fin.tail shift shift tail_shift shift_inj P R

theorem window_sv {m : ℕ} {P : win X (m + 1) → X → ℝ} {R : win X m → X → ℝ}
    (hPR : ∀ w c, P w c = R (Fin.tail w) c) (K : Set (win X m)) (n : ℕ) (w : win X (m + 1)) :
    sv (liftH shift P) (Fin.tail ⁻¹' K) n w = sv (liftH shift R) K n (Fin.tail w) :=
  sv_order tail_shift shift_inj hPR K n w

end FiveOrgans.MarkovOrderK
