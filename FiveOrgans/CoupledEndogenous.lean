import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Endogenous recursive viability: an agent and an environment that change each other

The earlier `Coupled*` modules fix the environment class and ask which capacities keep the agent
viable. Here the environment moves, the agent's response is rate-limited, and the agent may also
push the environment back toward itself (niche construction).

**1. Rate threshold (`rate_impossible`, `rate_sufficient`, `rate_iff`).** Let `e` be the tracking
error between the environment's target and the agent's internal model:

  e (n+1) = (1 − η)·e n + v − u n,   |u n| ≤ r.

Here `v ≥ 0` is the environment's drift per step, `r` is the agent's response capability (the
largest model update per step), and `η ∈ [0, 1]` is how strongly the agent shapes its environment.
Viability means `|e n| ≤ X` forever.
- If `v > r + η·X`, *every* response policy fails in finite time.
- If `v ≤ r + η·X`, the clipped policy `u = clip_r((1 − η)e + v)` keeps `|e| ≤ X` forever.
So a policy exists iff `v ≤ r + η·X`. Environmental change beyond response plus shaping capability
is fatal whatever the agent's configuration. Shaping the niche (`η > 0`) widens the viable region
by `η·X`.

**2. Static versus recursive viability under depletion (`depletion_kills`, `static_not_recursive`,
`exogenous_sustainable`).** Stock `S (n+1) = S n + q n − c` and regeneration `q (n+1) = q n − β·c`.
Consumption `c > 0` erodes the environment's regenerative capacity at rate `β > 0`.
- Configurations that are sustainable at time 0 (`q 0 ≥ c`) still die, from any initial stock.
- With `β = 0` (an exogenous environment) the same configuration is viable forever.
Viability that is checked against the current environment does not survive co-evolution.

**3. Reconfiguration can destroy viability (`mode_twice_zero`, `alternate_unbounded`,
`dwell_two_safe`).** Two linear modes on ℝ²: each, held for two steps, sends every state to 0.
Alternating them every step multiplies the state by 4 every two steps. A switching rule that
holds each chosen mode for at least two steps reaches 0 and stays there.
"Each configuration is viable" does not imply "switching among them is viable". This is a
dwell-time effect, as in switched-systems theory.

**4. The cost of keeping up (`response_lower`, `afford_impossible`, `accel_impossible`).** With a
time-varying drift `v n`, staying in the band forces the cumulative response up to step `n` to be at
least `Σ v − n·η·X − 2X`. If response capacity costs `κ` per unit per step from a finite reserve and
income `I`, and the drift eventually stays at or above `c > η·X + I/κ`, no policy is viable. An
accelerating environment `v n = v0 + a·n` (`a > 0`) defeats every finite income. Viability can be
bought for a while, but not forever. The pre-registered simulation (C5) finds an interior optimum:
too little investment and the drift outruns the agent; too much and the budget runs out first.

These are theorems about the stated difference equations. They say nothing directly about real
organisms or organisations.
-/

namespace FiveOrgans.CoupledEndogenous

/-! ## 1. Rate threshold -/

/-- An error path driven by drift `v`, shaping `η` and bounded responses `u` with `|u n| ≤ r`. -/
structure Path (η v r : ℝ) (e u : ℕ → ℝ) : Prop where
  step : ∀ n, e (n + 1) = (1 - η) * e n + v - u n
  bound : ∀ n, |u n| ≤ r

/-- While `|e| ≤ X`, each step raises the error by at least `v − r − η·X`. -/
lemma step_lower {η v r X : ℝ} {e u : ℕ → ℝ} (h : Path η v r e u) (hη : 0 ≤ η) (n : ℕ)
    (hn : |e n| ≤ X) : e n + (v - r - η * X) ≤ e (n + 1) := by
  have h1 := h.step n
  have h2 : u n ≤ r := (abs_le.mp (h.bound n)).2
  have h3 : e n ≤ X := (abs_le.mp hn).2
  have h4 : η * e n ≤ η * X := mul_le_mul_of_nonneg_left h3 hη
  rw [h1]; nlinarith

/-- **Impossibility.** If the environment drifts faster than response plus shaping capability
(`v > r + η·X`), every bounded-response policy leaves the viable band in finite time. -/
theorem rate_impossible {η v r X : ℝ} {e u : ℕ → ℝ} (h : Path η v r e u) (hη : 0 ≤ η)
    (hv : r + η * X < v) : ∃ n, X < |e n| := by
  by_contra hc
  push Not at hc
  set δ := v - r - η * X with hδ
  have hδp : 0 < δ := by linarith
  have grow : ∀ n : ℕ, e 0 + n * δ ≤ e n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have := step_lower h hη k (hc k)
      push_cast; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((X - e 0) / δ)
  have h1 := grow n
  have h2 : X - e 0 < n * δ := by
    have := (div_lt_iff₀ hδp).mp hn; linarith
  have h3 : e n ≤ X := (abs_le.mp (hc n)).2
  linarith

/-- The clipped response `clip_r(y) = max (−r) (min r y)`. -/
noncomputable def clip (r y : ℝ) : ℝ := max (-r) (min r y)

lemma clip_abs {r y : ℝ} (hr : 0 ≤ r) : |clip r y| ≤ r := by
  unfold clip; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-- The error path under the clipped policy. -/
noncomputable def clipPath (η v r e0 : ℝ) : ℕ → ℝ
  | 0 => e0
  | n + 1 => let y := (1 - η) * clipPath η v r e0 n + v; y - clip r y

/-- **Sufficiency.** If `v ≤ r + η·X` (with `v ≥ 0`, `0 ≤ η ≤ 1`, `r ≥ 0`), the clipped policy keeps
the error in the band forever. -/
theorem rate_sufficient {η v r X e0 : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hv0 : 0 ≤ v) (hr : 0 ≤ r)
    (hv : v ≤ r + η * X) (h0 : |e0| ≤ X) : ∀ n, |clipPath η v r e0 n| ≤ X := by
  intro n
  induction n with
  | zero => simpa [clipPath] using h0
  | succ k ih =>
    simp only [clipPath]
    set e := clipPath η v r e0 k
    have he := abs_le.mp ih
    have hX : 0 ≤ X := le_trans (abs_nonneg _) h0
    set y := (1 - η) * e + v with hy
    have hy_hi : y ≤ r + X := by nlinarith [he.2]
    have hy_lo : -X ≤ y := by nlinarith [he.1]
    unfold clip
    rw [abs_le]
    rcases le_total y r with h1 | h1
    · rw [min_eq_right h1]
      rcases le_total (-r) y with h2 | h2
      · rw [max_eq_right h2]; constructor <;> linarith
      · rw [max_eq_left h2]; constructor <;> linarith
    · rw [min_eq_left h1, max_eq_right (by linarith)]
      constructor <;> linarith

theorem clipPath_is_path (η v r e0 : ℝ) (hr : 0 ≤ r) :
    Path η v r (clipPath η v r e0) (fun n => clip r ((1 - η) * clipPath η v r e0 n + v)) where
  step n := by simp only [clipPath]
  bound n := clip_abs hr

/-- **Rate threshold.** A bounded-response policy that stays viable forever exists iff
`v ≤ r + η·X`. -/
theorem rate_iff {η v r X e0 : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hv0 : 0 ≤ v) (hr : 0 ≤ r)
    (h0 : |e0| ≤ X) :
    (∃ e u : ℕ → ℝ, Path η v r e u ∧ e 0 = e0 ∧ ∀ n, |e n| ≤ X) ↔ v ≤ r + η * X := by
  constructor
  · rintro ⟨e, u, hp, -, hall⟩
    by_contra hc; push Not at hc
    obtain ⟨n, hn⟩ := rate_impossible hp hη0 hc
    exact absurd (hall n) (not_le.mpr hn)
  · intro hv
    exact ⟨_, _, clipPath_is_path η v r e0 hr, rfl, rate_sufficient hη0 hη1 hv0 hr hv h0⟩

/-- Without niche construction (`η = 0`), the threshold is simply `v ≤ r`: response capability must
match the rate of environmental change, whatever the tolerance `X`. -/
theorem rate_iff_exogenous {v r X e0 : ℝ} (hv0 : 0 ≤ v) (hr : 0 ≤ r) (h0 : |e0| ≤ X) :
    (∃ e u : ℕ → ℝ, Path 0 v r e u ∧ e 0 = e0 ∧ ∀ n, |e n| ≤ X) ↔ v ≤ r := by
  have := rate_iff (η := 0) le_rfl zero_le_one hv0 hr h0 (X := X) (v := v)
  simpa using this

/-! ## 2. Static versus recursive viability under depletion -/

/-- Stock and regeneration capacity under consumption `c` with erosion rate `β`. -/
structure Depletion (β c : ℝ) (S q : ℕ → ℝ) : Prop where
  stock : ∀ n, S (n + 1) = S n + q n - c
  regen : ∀ n, q (n + 1) = q n - β * c

lemma regen_closed {β c : ℝ} {S q : ℕ → ℝ} (h : Depletion β c S q) (n : ℕ) :
    q n = q 0 - n * (β * c) := by
  induction n with
  | zero => simp
  | succ k ih => rw [h.regen, ih]; push_cast; ring

/-- If a sequence falls by at least 1 per step from some time on, it eventually goes negative. -/
lemma eventually_neg {S : ℕ → ℝ} (t1 : ℕ) (h : ∀ n, t1 ≤ n → S (n + 1) ≤ S n - 1) :
    ∃ n, S n < 0 := by
  have key : ∀ k : ℕ, S (t1 + k) ≤ S t1 - k := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
      have := h (t1 + j) (Nat.le_add_right _ _)
      rw [← add_assoc]; push_cast; linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (S t1)
  exact ⟨t1 + k, by linarith [key k]⟩

/-- **Depletion kills.** With erosion (`β·c > 0`), the stock goes negative in finite time from any
initial stock and any initial regeneration rate. -/
theorem depletion_kills {β c : ℝ} {S q : ℕ → ℝ} (h : Depletion β c S q) (hbc : 0 < β * c) :
    ∃ n, S n < 0 := by
  obtain ⟨t1, ht1⟩ := exists_nat_gt ((q 0 - c + 1) / (β * c))
  apply eventually_neg t1
  intro n hn
  have hq := regen_closed h n
  have hn' : (t1 : ℝ) ≤ n := by exact_mod_cast hn
  have : q 0 - c + 1 < n * (β * c) := by
    have := (div_lt_iff₀ hbc).mp ht1
    nlinarith
  rw [h.stock n]; linarith

/-- **Static viability does not imply recursive viability.** There is a configuration that is
exactly sustainable now (`q 0 = c`) with a large stock, yet it dies once its consumption
erodes regeneration. -/
theorem static_not_recursive : ∃ (S q : ℕ → ℝ), Depletion 1 1 S q ∧ q 0 ≥ 1 ∧ S 0 = 100 ∧
    ∃ n, S n < 0 := by
  let q : ℕ → ℝ := fun n => 1 - n
  let S : ℕ → ℝ := fun n => Nat.rec (100 : ℝ) (fun k s => s + q k - 1) n
  have hD : Depletion 1 1 S q := ⟨fun n => rfl, fun n => by simp [q]⟩
  exact ⟨S, q, hD, by simp [q], rfl, depletion_kills hD (by norm_num)⟩

/-- **Exogenous case.** Without erosion (`β = 0`) and with `q 0 ≥ c`, the stock never falls below
its initial level. -/
theorem exogenous_sustainable {c : ℝ} {S q : ℕ → ℝ} (h : Depletion 0 c S q) (hq : c ≤ q 0) :
    ∀ n, S 0 ≤ S n := by
  intro n
  induction n with
  | zero => exact le_refl _
  | succ k ih =>
    have := regen_closed h k
    rw [h.stock k, this]; simp; linarith

/-! ## 3. Reconfiguration can destroy viability -/

/-- Two linear modes on ℝ². -/
def mode : Bool → ℝ × ℝ → ℝ × ℝ
  | true, p => (2 * p.2, 0)
  | false, p => (0, 2 * p.1)

lemma mode_zero (b : Bool) : mode b (0, 0) = (0, 0) := by cases b <;> simp [mode]

/-- Each mode held for two consecutive steps sends every state to 0, so each fixed configuration
is viable. -/
theorem mode_twice_zero (b : Bool) (p : ℝ × ℝ) : mode b (mode b p) = (0, 0) := by
  cases b <;> simp [mode]

/-- The state under a switching schedule `σ`. -/
def run (σ : ℕ → Bool) (p : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => p
  | n + 1 => mode (σ n) (run σ p n)

/-- Alternating every step: two steps multiply the first coordinate by 4. -/
theorem alternate_two (x : ℝ) : mode true (mode false (x, 0)) = (4 * x, 0) := by
  simp [mode]; ring

theorem alternate_run (n : ℕ) :
    run (fun k => decide (k % 2 = 1)) (1, 0) (2 * n) = ((4 : ℝ) ^ n, 0) := by
  induction n with
  | zero => simp [run]
  | succ k ih =>
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [e]
    simp only [run]
    rw [ih]
    have h1 : (2 * k) % 2 = 0 := by omega
    have h2 : (2 * k + 1) % 2 = 1 := by omega
    simp [h1, h2, mode, pow_succ]; ring

/-- **Switching destroys viability.** Alternating the two (individually viable) modes leaves
every bounded band. -/
theorem alternate_unbounded (X : ℝ) : ∃ n, X < (run (fun k => decide (k % 2 = 1)) (1, 0) n).1 := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt X (by norm_num : (1 : ℝ) < 4)
  exact ⟨2 * n, by rw [alternate_run]; exact hn⟩

/-- Once the state is 0 it stays 0 under any schedule. -/
lemma run_zero_stays (σ : ℕ → Bool) (p : ℝ × ℝ) (m : ℕ) (hm : run σ p m = (0, 0)) :
    ∀ k, run σ p (m + k) = (0, 0) := by
  intro k
  induction k with
  | zero => simpa using hm
  | succ j ih => rw [← add_assoc]; simp only [run]; rw [ih, mode_zero]

/-- **Dwell time two is safe.** If the schedule holds some mode for two consecutive steps
(`σ m = σ (m+1)`), the state is 0 from step `m + 2` on, whatever the initial state. -/
theorem dwell_two_safe (σ : ℕ → Bool) (p : ℝ × ℝ) (m : ℕ) (hd : σ m = σ (m + 1)) :
    ∀ k, run σ p (m + 2 + k) = (0, 0) := by
  apply run_zero_stays
  show mode (σ (m + 1)) (mode (σ m) (run σ p m)) = (0, 0)
  rw [← hd]; exact mode_twice_zero _ _


/-! ## 4. The cost of keeping up -/

/-- A time-varying drift `v n` with responses `u n`. -/
structure PathV (η : ℝ) (v e u : ℕ → ℝ) : Prop where
  step : ∀ n, e (n + 1) = (1 - η) * e n + v n - u n

/-- **Cost lower bound.** Staying in the band forces the total response up to step `n` to be at least
the accumulated drift, less what shaping absorbs (`n·η·X`) and less the band width `2X`. -/
theorem response_lower {η X : ℝ} {v e u : ℕ → ℝ} (h : PathV η v e u) (hη : 0 ≤ η)
    (hall : ∀ n, |e n| ≤ X) (n : ℕ) :
    (∑ t ∈ Finset.range n, v t) - n * (η * X) - 2 * X ≤ ∑ t ∈ Finset.range n, u t := by
  have key : ∀ m : ℕ, (∑ t ∈ Finset.range m, v t) - m * (η * X) - (e m - e 0)
      ≤ ∑ t ∈ Finset.range m, u t := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, h.step k]
      have h3 : e k ≤ X := (abs_le.mp (hall k)).2
      have h4 : η * e k ≤ η * X := mul_le_mul_of_nonneg_left h3 hη
      push_cast; nlinarith
  have h1 := key n
  have h2 := abs_le.mp (hall n); have h0 := abs_le.mp (hall 0)
  linarith [h2.1, h2.2, h0.1, h0.2]

/-- Accumulated drift when the drift is nonnegative and at least `c` from time `T0` on. -/
lemma drift_sum_ge {v : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (T0 : ℕ) (hv0 : ∀ t, 0 ≤ v t)
    (hv : ∀ t, T0 ≤ t → c ≤ v t) (n : ℕ) : ((n : ℝ) - T0) * c ≤ ∑ t ∈ Finset.range n, v t := by
  induction n with
  | zero => simp; exact mul_nonneg (Nat.cast_nonneg _) hc
  | succ k ih =>
    rw [Finset.sum_range_succ]
    by_cases hk : T0 ≤ k
    · have := hv k hk; push_cast; nlinarith
    · push_neg at hk
      have hk' : ((k : ℝ) + 1) ≤ T0 := by exact_mod_cast hk
      have hs : 0 ≤ ∑ t ∈ Finset.range k, v t := Finset.sum_nonneg (fun t _ => hv0 t)
      have : ((↑(k + 1) : ℝ) - T0) * c ≤ 0 := by
        push_cast; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hc
      linarith [hv0 k]

/-- **Affordability threshold.** Response capacity `r n` costs `κ·r n` per step, paid from a reserve
`R0` and income `I`. If the drift eventually stays at or above `c` with `κ·c > κ·η·X + I`,
no policy keeps both the error band and a nonnegative reserve forever. An accelerating
environment (`v n → ∞`) meets this for every finite income, so in such an environment viability
cannot be bought indefinitely. -/
theorem afford_impossible {η X κ I R0 c : ℝ} {v e u r : ℕ → ℝ} (h : PathV η v e u) (hη : 0 ≤ η)
    (hκ : 0 < κ) (hc : 0 ≤ c) (T0 : ℕ) (hv0 : ∀ t, 0 ≤ v t) (hv : ∀ t, T0 ≤ t → c ≤ v t)
    (hu : ∀ t, |u t| ≤ r t) (hgap : κ * (η * X) + I < κ * c) :
    ¬ ((∀ n, |e n| ≤ X) ∧ ∀ n, 0 ≤ R0 + n * I - κ * ∑ t ∈ Finset.range n, r t) := by
  rintro ⟨hall, hbud⟩
  have hX : 0 ≤ X := le_trans (abs_nonneg _) (hall 0)
  set g := κ * c - κ * (η * X) - I with hg
  have hgp : 0 < g := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((R0 + κ * (T0 * c) + κ * (2 * X)) / g)
  have h1 := response_lower h hη hall n
  have h2 := drift_sum_ge hc T0 hv0 hv n
  have h3 : ∑ t ∈ Finset.range n, u t ≤ ∑ t ∈ Finset.range n, r t :=
    Finset.sum_le_sum (fun t _ => le_trans (le_abs_self _) (hu t))
  have h4 := hbud n
  have h5 : R0 + κ * (T0 * c) + κ * (2 * X) < n * g := by
    have := (div_lt_iff₀ hgp).mp hn; linarith
  have h6 : κ * (((n : ℝ) - T0) * c - n * (η * X) - 2 * X) ≤ κ * ∑ t ∈ Finset.range n, r t := by
    apply mul_le_mul_of_nonneg_left _ hκ.le; linarith
  nlinarith

/-- An accelerating environment `v n = v0 + a·n` (`a > 0`, `v0 ≥ 0`) defeats every finite income. -/
theorem accel_impossible {η X κ I R0 v0 a : ℝ} {e u r : ℕ → ℝ}
    (h : PathV η (fun n => v0 + a * n) e u) (hη : 0 ≤ η) (hκ : 0 < κ) (hv0 : 0 ≤ v0) (ha : 0 < a)
    (hu : ∀ t, |u t| ≤ r t) :
    ¬ ((∀ n, |e n| ≤ X) ∧ ∀ n, 0 ≤ R0 + n * I - κ * ∑ t ∈ Finset.range n, r t) := by
  rintro ⟨hall, hbud⟩
  have hX : 0 ≤ X := le_trans (abs_nonneg _) (hall 0)
  set c := η * X + |I| / κ + 1 with hcdef
  have hc : 0 ≤ c := by positivity
  obtain ⟨T0, hT0⟩ := exists_nat_gt (c / a)
  have hv : ∀ t, T0 ≤ t → c ≤ v0 + a * t := by
    intro t ht
    have : (T0 : ℝ) ≤ t := by exact_mod_cast ht
    have := (div_lt_iff₀ ha).mp hT0; nlinarith
  have hgap : κ * (η * X) + I < κ * c := by
    have : κ * (|I| / κ) = |I| := by field_simp
    have := le_abs_self I
    rw [hcdef]; nlinarith
  exact afford_impossible h hη hκ hc T0 (fun t => by positivity) hv hu hgap ⟨hall, hbud⟩

end FiveOrgans.CoupledEndogenous
