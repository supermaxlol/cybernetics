import FiveOrgans.SensingRate

/-!
# Scrambled messages: worst case versus average case (T4, T5 of note 14)

Same world as `SensingRate`: `x' = a x + u + w`, `|w| ≤ d`, death when `|x| > r`, one of `M`
messages per step, causal strategies (`SensingRate.Strat`). Now step `n` may be *scrambled*: the
controller receives an arbitrary message `f n` instead of the encoder's.

* `scramble_iff` (T4): if the scrambling pattern and the false messages are adversarial, some
  strategy survives for ever, from every start, against every disturbance **iff `|a| r + d ≤ r`**,
  the condition for surviving with no information at all. The adversary needs to scramble only the
  first step (`first_scrambled_fatal`). So in the worst case any scrambling makes the messages
  worthless, whatever `M` is.
* `separation` (T5): with independent scrambling of each step with probability `η`, there is a
  strategy (the counting one, when `M` meets `SensingRate.forever_iff`) whose probability of
  surviving `T` steps is at least `(1 - η)^T` for every start, disturbance and false message;
  yet when `r < |a| r + d`, every strategy has, for some start and disturbance, survival
  probability at most `1 - η`. Worst-case viability fails; average-case survival does not.

Scope. Scalar, linear, unlimited actuation; scrambling independent of the state; the lower bound
`(1 - η)^T` counts only unscrambled histories and is loose (the simulations in
`analysis/sensing` show survival well above it). Nothing here is about real systems.
-/

namespace FiveOrgans.Scrambling
open FiveOrgans.SensingRate Finset

variable {M : ℕ} {a r d : ℝ}

/-- States and received messages; step `n` is scrambled when `c n`, and then the message is `f n`. -/
noncomputable def hist (a : ℝ) (S : Strat M) (c : ℕ → Bool) (f : ℕ → Fin M) (x₀ : ℝ)
    (w : ℕ → ℝ) : ℕ → List ℝ × List (Fin M)
  | 0 => ([x₀], [if c 0 then f 0 else S.enc [x₀]])
  | n + 1 =>
    let h := hist a S c f x₀ w n
    let x := a * h.1.headD 0 + S.act h.2 + w n
    (x :: h.1, (if c (n + 1) then f (n + 1) else S.enc (x :: h.1)) :: h.2)

/-- Current state. -/
noncomputable def st (a : ℝ) (S : Strat M) (c : ℕ → Bool) (f : ℕ → Fin M) (x₀ : ℝ)
    (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  (hist a S c f x₀ w n).1.headD 0

theorem st_succ (S : Strat M) (c : ℕ → Bool) (f : ℕ → Fin M) (x₀ : ℝ) (w : ℕ → ℝ) (n : ℕ) :
    st a S c f x₀ w (n + 1) = a * st a S c f x₀ w n + S.act (hist a S c f x₀ w n).2 + w n :=
  rfl

theorem st_one (S : Strat M) {c : ℕ → Bool} (hc : c 0 = true) (f : ℕ → Fin M) (x₀ : ℝ)
    (w : ℕ → ℝ) : st a S c f x₀ w 1 = a * x₀ + S.act [f 0] + w 0 := by
  simp [st, hist, hc]

/-- With no scrambling the history is the one of `SensingRate`. -/
theorem hist_clean (S : Strat M) (f : ℕ → Fin M) (x₀ : ℝ) (w : ℕ → ℝ) (n : ℕ) :
    hist a S (fun _ => false) f x₀ w n = SensingRate.hist a S x₀ w n := by
  induction n with
  | zero => simp [hist, SensingRate.hist]
  | succ n ih => simp only [hist, SensingRate.hist, ih]; rfl

/-- **Scrambling the first message is fatal** unless the blind condition holds. The start and
disturbance depend only on the strategy and the false first message, not on later scrambling. -/
theorem first_scrambled_fatal (hr : 0 ≤ r) (hd : 0 ≤ d) (h : r < |a| * r + d) (S : Strat M)
    (f : ℕ → Fin M) :
    ∃ x₀, |x₀| ≤ r ∧ ∃ w : ℕ → ℝ, (∀ n, |w n| ≤ d) ∧
      ∀ c : ℕ → Bool, c 0 = true → r < |st a S c f x₀ w 1| := by
  have hr' : |r| ≤ r := by rw [abs_of_nonneg hr]
  have hr'' : |-r| ≤ r := by rw [abs_neg, abs_of_nonneg hr]
  have hdd : ∀ n : ℕ, |(fun _ : ℕ => d) n| ≤ d := fun _ => by simp [abs_of_nonneg hd]
  have hdn : ∀ n : ℕ, |(fun _ : ℕ => -d) n| ≤ d := fun _ => by simp [abs_of_nonneg hd]
  rcases le_or_gt 0 (S.act [f 0]) with hu | hu <;> rcases le_or_gt 0 a with ha | ha
  · refine ⟨r, hr', fun _ => d, hdd, fun c hc => ?_⟩
    rw [st_one S hc]; rw [abs_of_nonneg ha] at h
    exact lt_abs.2 (Or.inl (by linarith))
  · refine ⟨-r, hr'', fun _ => d, hdd, fun c hc => ?_⟩
    rw [st_one S hc]; rw [abs_of_neg ha] at h
    exact lt_abs.2 (Or.inl (by linarith))
  · refine ⟨-r, hr'', fun _ => -d, hdn, fun c hc => ?_⟩
    rw [st_one S hc]; rw [abs_of_nonneg ha] at h
    exact lt_abs.2 (Or.inr (by linarith))
  · refine ⟨r, hr', fun _ => -d, hdn, fun c hc => ?_⟩
    rw [st_one S hc]; rw [abs_of_neg ha] at h
    exact lt_abs.2 (Or.inr (by linarith))

/-- **T4.** Against adversarial scrambling, survival for ever is possible iff it is possible blind. -/
theorem scramble_iff (hM : 0 < M) (hr : 0 < r) (hd : 0 ≤ d) :
    (∃ S : Strat M, ∀ (c : ℕ → Bool) (f : ℕ → Fin M) (x₀ : ℝ), |x₀| ≤ r →
        ∀ w : ℕ → ℝ, (∀ n, |w n| ≤ d) → ∀ n, |st a S c f x₀ w n| ≤ r)
      ↔ |a| * r + d ≤ r := by
  constructor
  · rintro ⟨S, hS⟩
    by_contra hc; push Not at hc
    obtain ⟨x₀, hx, w, hw, hk⟩ := first_scrambled_fatal hr.le hd hc S (fun _ => ⟨0, hM⟩)
    exact absurd (hS (fun _ => true) _ x₀ hx w hw 1) (not_le.2 (hk _ rfl))
  · intro h
    refine ⟨⟨fun _ => ⟨0, hM⟩, fun _ => 0⟩, fun c f x₀ hx w hw n => ?_⟩
    induction n with
    | zero => simpa [st, hist] using hx
    | succ n ih =>
      rw [st_succ]
      show |a * _ + 0 + w n| ≤ r
      rw [add_zero]
      calc _ ≤ |a * _| + |w n| := abs_add_le _ _
        _ ≤ |a| * r + d := by
            rw [abs_mul]; exact add_le_add (mul_le_mul_of_nonneg_left ih (abs_nonneg a)) (hw n)
        _ ≤ r := h

/-! ### Random scrambling: each of the first `T` steps independently with probability `η` -/

/-- Probability of a scrambling pattern of the first `T` steps. -/
def wt (η : ℝ) {T : ℕ} (c : Fin T → Bool) : ℝ := ∏ i, if c i then η else 1 - η

/-- The pattern as a function on all steps (no scrambling after `T`). -/
def ext {T : ℕ} (c : Fin T → Bool) (n : ℕ) : Bool := if h : n < T then c ⟨n, h⟩ else false

theorem wt_nonneg {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) {T : ℕ} (c : Fin T → Bool) : 0 ≤ wt η c :=
  prod_nonneg fun i _ => by split <;> linarith

theorem wt_sum (η : ℝ) (T : ℕ) : ∑ c : Fin T → Bool, wt η c = 1 := by
  unfold wt
  refine (Fintype.prod_sum (fun (_ : Fin T) (b : Bool) => if b then η else 1 - η)).symm.trans ?_
  simp

theorem wt_clean (η : ℝ) (T : ℕ) : wt η (fun _ : Fin T => false) = (1 - η) ^ T := by
  simp [wt]

/-- The first step is scrambled with probability `η`. -/
theorem wt_first (η : ℝ) (k : ℕ) :
    ∑ c : Fin (k + 1) → Bool, (if c 0 then wt η c else 0) = η := by
  have e : ∀ c : Fin (k + 1) → Bool, (if c 0 then wt η c else 0) =
      ∏ i, (if i = 0 then (if c i then η else 0) else (if c i then η else 1 - η)) := by
    intro c
    rw [Fin.prod_univ_succ]; unfold wt; rw [Fin.prod_univ_succ]
    cases c 0 <;> simp [Fin.succ_ne_zero]
  simp_rw [e]
  refine (Fintype.prod_sum (fun (i : Fin (k + 1)) (b : Bool) =>
    if i = 0 then (if b then η else 0) else (if b then η else 1 - η))).symm.trans ?_
  rw [Fin.prod_univ_succ]; simp [Fin.succ_ne_zero]

/-- Survives the first `T` steps (states `0..T`). -/
def Surv (a r : ℝ) (S : Strat M) {T : ℕ} (c : Fin T → Bool) (f : ℕ → Fin M) (x₀ : ℝ)
    (w : ℕ → ℝ) : Prop :=
  ∀ n ≤ T, |st a S (ext c) f x₀ w n| ≤ r

open Classical in
/-- Probability of surviving `T` steps over the random scrambling. -/
noncomputable def survP (a r η : ℝ) (S : Strat M) (T : ℕ) (f : ℕ → Fin M) (x₀ : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ c : Fin T → Bool, wt η c * (if Surv a r S c f x₀ w then 1 else 0)

/-- **T5, average-versus-worst-case separation.** -/
theorem separation (hM : 0 < M) (hr : 0 < r) (hd : 0 ≤ d) {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1)
    (k : ℕ) :
    -- the counting strategy survives with probability at least (1-η)^(k+1)
    (|a| * r + M * d ≤ M * r → ∃ S : Strat M, ∀ f x₀, |x₀| ≤ r → ∀ w : ℕ → ℝ,
        (∀ n, |w n| ≤ d) → (1 - η) ^ (k + 1) ≤ survP a r η S (k + 1) f x₀ w) ∧
    -- but when blind survival is impossible, every strategy can be held to at most 1 - η
    (r < |a| * r + d → ∀ (S : Strat M) (f : ℕ → Fin M), ∃ x₀, |x₀| ≤ r ∧ ∃ w : ℕ → ℝ,
        (∀ n, |w n| ≤ d) ∧ survP a r η S (k + 1) f x₀ w ≤ 1 - η) := by
  classical
  refine ⟨fun h => ?_, fun h S f => ?_⟩
  · obtain ⟨S, hS⟩ := (forever_iff hM hr hd).2 h
    refine ⟨S, fun f x₀ hx w hw => ?_⟩
    have hs : Surv a r S (fun _ : Fin (k + 1) => false) f x₀ w := by
      intro n _
      have : ext (fun _ : Fin (k + 1) => false) = fun _ => false := by
        funext m; simp [ext]
      rw [this, st, hist_clean]; exact hS x₀ hx w hw n
    calc (1 - η) ^ (k + 1) = wt η (fun _ : Fin (k + 1) => false) *
          (if Surv a r S (fun _ : Fin (k + 1) => false) f x₀ w then 1 else 0) := by
            rw [if_pos hs, mul_one, wt_clean]
      _ ≤ survP a r η S (k + 1) f x₀ w :=
          single_le_sum (f := fun c => wt η c * (if Surv a r S c f x₀ w then 1 else 0))
            (fun c _ => mul_nonneg (wt_nonneg h0 h1 c) (by split <;> norm_num)) (mem_univ _)
  · obtain ⟨x₀, hx, w, hw, hk⟩ := first_scrambled_fatal hr.le hd h S f
    refine ⟨x₀, hx, w, hw, ?_⟩
    have hle : ∀ c : Fin (k + 1) → Bool, wt η c * (if Surv a r S c f x₀ w then 1 else 0)
        ≤ wt η c - (if c 0 then wt η c else 0) := by
      intro c
      by_cases hc : c 0 = true
      · have : ¬ Surv a r S c f x₀ w := fun hs =>
          absurd (hs 1 (by omega)) (not_le.2 (hk (ext c) (by simp [ext, hc])))
        simp [this, hc]
      · simp only [hc, if_false, sub_zero]
        have := wt_nonneg h0 h1 c
        split
        · simp
        · simpa using this
    calc survP a r η S (k + 1) f x₀ w ≤ ∑ c : Fin (k + 1) → Bool,
          (wt η c - (if c 0 then wt η c else 0)) := sum_le_sum fun c _ => hle c
      _ = 1 - η := by rw [sum_sub_distrib, wt_sum, wt_first]

end FiveOrgans.Scrambling
