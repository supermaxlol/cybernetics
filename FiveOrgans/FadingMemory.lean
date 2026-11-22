import FiveOrgans.MarkovOrderK

/-!
# Fading memory: finite-order approximation with an explicit survival gap

`MarkovOrderK` is exact: the extra history is irrelevant or it is not. Real processes may have
memory that matters but fades. Setting as in `MarkovOrderK`: long histories `H`, short `S`,
forgetting map `π`, shifts with `π (push h c) = pushS (π h) c`.

* `liftH_rowsum`, `liftH_nonneg` — the history chain is (sub)stochastic when `P` is.
* `liftH_defect_le` — the lumpability defect of the long chain against the short chain built
  from `R` is at most the one-step memory error `Σ_c |P h c − R (π h) c|`.
* `fading_sv` — **if the memory error is `≤ η` at every long history, survival of the long-history
  chain and of the short-history chain differ by at most `n η` after `n` steps.**
* `memory_var_bound` — taking `R` from any representative long history, it is enough that two
  long histories with the same short part never differ by more than `β` in next-step law
  (ℓ¹): then `η = β`.
* `window_fading_sv` — the same for windows (order `m + 2` against order `m + 1`).
* `geometric_order` — if the memory variation at order `m` is `≤ C ρ^m` with `ρ < 1`, then for
  any horizon `n` and tolerance `ε > 0` some finite order `m` has survival gap `≤ ε`.

Reading. A finite micro level is a good stand-in for a long-memory system exactly to the extent
that its memory variation `β` is small relative to `1/n`. On hourly crypto volatility the measured
history effect stays near 0.2 from order 1 to 6 (`analysis/EXPLORE_MARKOV_ORDER_2026-11-22.md`),
so this bound gives nothing useful there for any `n ≥ 5`. That is a measured `β`, not a proof
about the true process.
-/

namespace FiveOrgans.FadingMemory
open Finset Classical FiveOrgans.CrossScaleMarkov FiveOrgans.MarkovOrderK

variable {H S X : Type*} [Fintype H] [Fintype S] [Fintype X]

omit [Fintype H] [Fintype S] in
theorem liftH_nonneg {push : H → X → H} {P : H → X → ℝ} (hP : ∀ h c, 0 ≤ P h c) (h h' : H) :
    0 ≤ liftH push P h h' :=
  sum_nonneg fun c _ => by split_ifs <;> first | exact hP h c | exact le_rfl

omit [Fintype S] in
theorem liftH_rowsum (push : H → X → H) (P : H → X → ℝ) (h : H) :
    ∑ h', liftH push P h h' = ∑ c, P h c := by
  unfold liftH
  rw [Finset.sum_comm]
  exact sum_congr rfl fun c _ => by rw [Finset.sum_ite_eq]; simp

theorem liftH_defect_le (π : H → S) (push : H → X → H) (pushS : S → X → S)
    (hc : ∀ h c, π (push h c) = pushS (π h) c) (P : H → X → ℝ) (R : S → X → ℝ) (h : H) :
    ∑ s', |∑ h' ∈ univ.filter (fun h' => π h' = s'), liftH push P h h'
        - liftH pushS R (π h) s'| ≤ ∑ c, |P h c - R (π h) c| := by
  rw [show (∑ s', |∑ h' ∈ univ.filter (fun h' => π h' = s'), liftH push P h h'
        - liftH pushS R (π h) s'|)
      = ∑ s', |∑ c, (if pushS (π h) c = s' then P h c - R (π h) c else 0)| from
    sum_congr rfl fun s' _ => by
      rw [liftH_blk π push pushS hc]; unfold liftH; rw [← sum_sub_distrib]
      congr 1; exact sum_congr rfl fun c _ => by split_ifs <;> simp]
  calc ∑ s', |∑ c, (if pushS (π h) c = s' then P h c - R (π h) c else 0)|
      ≤ ∑ s', ∑ c, (if pushS (π h) c = s' then |P h c - R (π h) c| else 0) :=
        sum_le_sum fun s' _ => (abs_sum_le_sum_abs _ _).trans_eq
          (sum_congr rfl fun c _ => by split_ifs <;> simp)
    _ = ∑ c, |P h c - R (π h) c| := by
        rw [Finset.sum_comm]
        exact sum_congr rfl fun c _ => by rw [Finset.sum_ite_eq]; simp

/-- **Survival gap under fading memory.** -/
theorem fading_sv {π : H → S} {push : H → X → H} {pushS : S → X → S}
    (hc : ∀ h c, π (push h c) = pushS (π h) c) {P : H → X → ℝ} {R : S → X → ℝ}
    (hP : ∀ h c, 0 ≤ P h c) (hProw : ∀ h, ∑ c, P h c ≤ 1)
    (hR : ∀ s c, 0 ≤ R s c) (hRrow : ∀ s, ∑ c, R s c ≤ 1) {η : ℝ}
    (hη : ∀ h, ∑ c, |P h c - R (π h) c| ≤ η) (K : Set S) (n : ℕ) (h : H) :
    |sv (liftH push P) (π ⁻¹' K) n h - sv (liftH pushS R) K n (π h)| ≤ n * η :=
  sv_approx_lump (liftH_nonneg hP) (fun h => (liftH_rowsum push P h).trans_le (hProw h))
    (liftH_nonneg hR) (fun s => (liftH_rowsum pushS R s).trans_le (hRrow s))
    (fun h => (liftH_defect_le π push pushS hc P R h).trans (hη h)) K n h

/-- **Memory variation is enough:** take `R` from a representative long history. -/
theorem memory_var_bound {π : H → S} {push : H → X → H} {pushS : S → X → S}
    (hc : ∀ h c, π (push h c) = pushS (π h) c) {P : H → X → ℝ}
    (hP : ∀ h c, 0 ≤ P h c) (hProw : ∀ h, ∑ c, P h c ≤ 1)
    (rep : S → H) (hrep : ∀ s, π (rep s) = s) {β : ℝ}
    (hβ : ∀ h h', π h = π h' → ∑ c, |P h c - P h' c| ≤ β) (K : Set S) (n : ℕ) (h : H) :
    |sv (liftH push P) (π ⁻¹' K) n h
      - sv (liftH pushS (fun s c => P (rep s) c)) K n (π h)| ≤ n * β :=
  fading_sv hc hP hProw (fun s c => hP (rep s) c) (fun s => hProw (rep s))
    (fun h => hβ h (rep (π h)) (hrep (π h)).symm) K n h

/-- Windows: order `m + 2` against order `m + 1`. -/
theorem window_fading_sv {m : ℕ} {P : win X (m + 1) → X → ℝ} {R : win X m → X → ℝ}
    (hP : ∀ w c, 0 ≤ P w c) (hProw : ∀ w, ∑ c, P w c ≤ 1)
    (hR : ∀ s c, 0 ≤ R s c) (hRrow : ∀ s, ∑ c, R s c ≤ 1) {η : ℝ}
    (hη : ∀ w, ∑ c, |P w c - R (Fin.tail w) c| ≤ η) (K : Set (win X m)) (n : ℕ)
    (w : win X (m + 1)) :
    |sv (liftH shift P) (Fin.tail ⁻¹' K) n w - sv (liftH shift R) K n (Fin.tail w)| ≤ n * η :=
  fading_sv tail_shift hP hProw hR hRrow hη K n w

/-- **Geometric fading suffices:** some finite order meets any tolerance at any horizon. -/
theorem geometric_order {C ρ ε : ℝ} (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (hε : 0 < ε)
    (n : ℕ) : ∃ m : ℕ, n * (C * ρ ^ m) ≤ ε := by
  have hpos : 0 < ε / (n * C + 1) := by positivity
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos hρ
  refine ⟨m, ?_⟩
  have hρm : 0 ≤ ρ ^ m := pow_nonneg hρ0 m
  have h1 : (n * C + 1) * ρ ^ m < ε := by
    rwa [lt_div_iff₀ (by positivity), mul_comm] at hm
  nlinarith

end FiveOrgans.FadingMemory
