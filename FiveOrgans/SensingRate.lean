import FiveOrgans.CompressionInfo
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# How many messages a survivor must receive: the counting sensing-rate threshold

State `x' = a x + u + w`, disturbance `|w| ≤ d`, death when `|x| > r`. A sensor sends one of `M`
messages per step.

* `step_iff`: one safe step from every `|x| ≤ r` is possible iff `|a| r + M d ≤ M r`, that is
  `|a| r / M + d ≤ r`.
* `forever_iff`: the same inequality is exactly what is needed to survive **forever, from every
  start in `[-r, r]`, against every bounded disturbance, for every causal strategy** (the encoder
  may remember all past states, the controller all past messages). Memory does not lower the
  requirement, because the first message already has to cope with the whole interval.
* `messages_iff`: equivalently `M ≥ |a| r / (r − d)`. With `d = 0` this is `M ≥ |a|`, the
  worst-case counting form of the data-rate number `log₂ |a|`.
* `bits_forever_iff`: `b` bits per step suffice iff `|a| r ≤ 2 ^ b (r − d)`.
* `blind_dies`: one message (no information) fails when `|a| ≥ 1` and `d > 0`.
* `sensor_error_iff`: with a continuous reading `y = x + e`, `|e| ≤ s ≤ r`, a safe memoryless rule
  exists iff `|a| s + d ≤ r`. So the critical sensor error is `(r − d)/|a|`
  (`critical_error`), which is the half-width of a message cell at the message threshold.

Scope. Scalar, linear, unlimited actuation, no delay. The start is unknown in the whole interval;
the *known*-start case (same threshold when `d > 0`) is `KnownStart.known_start_iff`. Worst case only; random disturbances can
be survived for a long time below the threshold. The sensor-error result is for memoryless rules.
The data-rate theorem itself (asymptotic stabilisation) is not proved here.
-/

namespace FiveOrgans.SensingRate
open MeasureTheory Set

variable {M : ℕ} {a r d s : ℝ}

/-- Centre of message cell `i` of `[-r, r]`. -/
noncomputable def centre (M : ℕ) (r : ℝ) (i : Fin M) : ℝ := -r + (2 * (i : ℕ) + 1) * (r / M)

theorem exists_cell (hM : 0 < M) (hr : 0 < r) {x : ℝ} (hx : |x| ≤ r) :
    ∃ i : Fin M, |x - centre M r i| ≤ r / M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨h1, h2⟩ := abs_le.1 hx
  set t := (x + r) * M / (2 * r) with ht
  have ht0 : 0 ≤ t := by rw [ht]; apply div_nonneg (mul_nonneg (by linarith) hM'.le); linarith
  have htM : t ≤ M := by
    rw [ht, div_le_iff₀ (by linarith)]; nlinarith
  have hxt : x = -r + 2 * t * (r / M) := by rw [ht]; field_simp; ring
  have key : ∃ i : ℕ, i < M ∧ (i : ℝ) ≤ t ∧ t ≤ i + 1 := by
    rcases htM.lt_or_eq with h | h
    · exact ⟨⌊t⌋₊, (Nat.floor_lt ht0).2 h, Nat.floor_le ht0, (Nat.lt_floor_add_one t).le⟩
    · refine ⟨M - 1, by omega, ?_, ?_⟩ <;> rw [h, Nat.cast_sub hM] <;> simp
  obtain ⟨i, hi, hl, hu⟩ := key
  refine ⟨⟨i, hi⟩, ?_⟩
  have hq : 0 ≤ r / M := (div_pos hr hM').le
  have : x - centre M r ⟨i, hi⟩ = (2 * (t - i) - 1) * (r / M) := by
    rw [hxt]; simp only [centre]; ring
  rw [this, abs_mul, abs_of_nonneg hq]
  have hab : |2 * (t - i) - 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  nlinarith

/-- Nearest-cell encoder. -/
noncomputable def cell (hM : 0 < M) (hr : 0 < r) (x : ℝ) : Fin M := by
  classical
  exact if h : |x| ≤ r then (exists_cell hM hr h).choose else ⟨0, hM⟩

theorem cell_spec (hM : 0 < M) (hr : 0 < r) {x : ℝ} (hx : |x| ≤ r) :
    |x - centre M r (cell hM hr x)| ≤ r / M := by
  unfold cell; rw [dite_eq_left hx]; exact (exists_cell hM hr hx).choose_spec

theorem cell_safe (hM : 0 < M) (hr : 0 < r) (h : |a| * r + M * d ≤ M * r) {x w : ℝ}
    (hx : |x| ≤ r) (hw : |w| ≤ d) :
    |a * x + -(a * centre M r (cell hM hr x)) + w| ≤ r := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have e : a * x + -(a * centre M r (cell hM hr x)) + w
      = a * (x - centre M r (cell hM hr x)) + w := by ring
  rw [e]
  have h1 := cell_spec hM hr hx
  have h2 : |a| * (r / M) + d ≤ r := by
    have : |a| * (r / M) + d = (|a| * r + M * d) / M := by field_simp
    rw [this, div_le_iff₀ hM']; linarith
  calc _ ≤ |a * (x - centre M r (cell hM hr x))| + |w| := abs_add_le _ _
    _ ≤ |a| * (r / M) + d := by
      rw [abs_mul]; exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg a)) hw
    _ ≤ r := h2

/-- Volume count: if every `|x| ≤ r` is safe for the action of its message, then
`|a| r ≤ M (r − d)`. -/
theorem count_needed (hr : 0 < r) (hd : 0 ≤ d) (enc : ℝ → Fin M) (act : Fin M → ℝ)
    (h : ∀ x, |x| ≤ r → ∀ w, |w| ≤ d → |a * x + act (enc x) + w| ≤ r) :
    |a| * r + M * d ≤ M * r := by
  have tight : ∀ x, |x| ≤ r → |a * x + act (enc x)| ≤ r - d := by
    intro x hx
    have h1 := abs_le.1 (h x hx d (by rw [abs_of_nonneg hd]))
    have h2 := abs_le.1 (h x hx (-d) (by rw [abs_neg, abs_of_nonneg hd]))
    exact abs_le.2 ⟨by linarith [h2.1], by linarith [h1.2]⟩
  have hrd : 0 ≤ r - d := (abs_nonneg _).trans (tight 0 (by simpa using hr.le))
  rcases eq_or_ne a 0 with ha | ha
  · have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    rw [ha]; simp; nlinarith
  have ha' : 0 < |a| := abs_pos.2 ha
  set q := (r - d) / |a| with hq
  have hq0 : 0 ≤ q := div_nonneg hrd ha'.le
  have hsub : Icc (-r) r ⊆ ⋃ m : Fin M, Icc (-(act m / a) - q) (-(act m / a) + q) := by
    intro x hx
    have hx' := tight x (abs_le.2 ⟨hx.1, hx.2⟩)
    refine mem_iUnion.2 ⟨enc x, ?_⟩
    have e : |x + act (enc x) / a| ≤ q := by
      rw [hq, le_div_iff₀ ha', ← abs_mul]
      have : (x + act (enc x) / a) * a = a * x + act (enc x) := by field_simp
      rwa [this]
    obtain ⟨e1, e2⟩ := abs_le.1 e
    exact ⟨by linarith, by linarith⟩
  have hv : ENNReal.ofReal (2 * r) ≤ ENNReal.ofReal (M * (2 * q)) := by
    calc ENNReal.ofReal (2 * r) = volume (Icc (-r) r) := by
          rw [Real.volume_Icc]; congr 1; ring
      _ ≤ volume (⋃ m : Fin M, Icc (-(act m / a) - q) (-(act m / a) + q)) := measure_mono hsub
      _ ≤ ∑ m : Fin M, volume (Icc (-(act m / a) - q) (-(act m / a) + q)) :=
          measure_iUnion_fintype_le _ _
      _ = ∑ _m : Fin M, ENNReal.ofReal (2 * q) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Real.volume_Icc]; congr 1; ring
      _ = ENNReal.ofReal (M * (2 * q)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg M), ENNReal.ofReal_natCast]
  have hfin : 2 * r ≤ M * (2 * q) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hv
  have hqa : |a| * q = r - d := by rw [hq]; field_simp
  nlinarith

/-- **One safe step iff enough messages.** -/
theorem step_iff (hM : 0 < M) (hr : 0 < r) (hd : 0 ≤ d) :
    (∃ (enc : ℝ → Fin M) (act : Fin M → ℝ),
      ∀ x, |x| ≤ r → ∀ w, |w| ≤ d → |a * x + act (enc x) + w| ≤ r)
      ↔ |a| * r + M * d ≤ M * r := by
  constructor
  · rintro ⟨enc, act, h⟩; exact count_needed hr hd enc act h
  · intro h
    exact ⟨cell hM hr, fun m => -(a * centre M r m), fun x hx w hw => cell_safe hM hr h hx hw⟩

/-! ### All causal strategies, for ever -/

/-- A causal strategy: the encoder sees all states so far (newest first), the controller all
messages so far (newest first). -/
structure Strat (M : ℕ) where
  enc : List ℝ → Fin M
  act : List (Fin M) → ℝ

/-- States and messages so far. -/
noncomputable def hist (a : ℝ) (S : Strat M) (x₀ : ℝ) (w : ℕ → ℝ) : ℕ → List ℝ × List (Fin M)
  | 0 => ([x₀], [S.enc [x₀]])
  | n + 1 =>
    let h := hist a S x₀ w n
    let x := a * h.1.headD 0 + S.act h.2 + w n
    (x :: h.1, S.enc (x :: h.1) :: h.2)

/-- Current state. -/
noncomputable def st (a : ℝ) (S : Strat M) (x₀ : ℝ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  (hist a S x₀ w n).1.headD 0

/-- Survives for ever, from every start in the safe interval, against every bounded disturbance. -/
def Viable (a r d : ℝ) (S : Strat M) : Prop :=
  ∀ x₀, |x₀| ≤ r → ∀ w : ℕ → ℝ, (∀ n, |w n| ≤ d) → ∀ n, |st a S x₀ w n| ≤ r

/-- **The counting sensing-rate theorem.** -/
theorem forever_iff (hM : 0 < M) (hr : 0 < r) (hd : 0 ≤ d) :
    (∃ S : Strat M, Viable a r d S) ↔ |a| * r + M * d ≤ M * r := by
  constructor
  · rintro ⟨S, hS⟩
    refine count_needed hr hd (fun x => S.enc [x]) (fun m => S.act [m]) fun x hx w hw => ?_
    simpa [st, hist] using hS x hx (fun _ => w) (fun _ => hw) 1
  · intro h
    refine ⟨⟨fun l => cell hM hr (l.headD 0), fun l => match l with
      | [] => 0
      | m :: _ => -(a * centre M r m)⟩, fun x₀ hx w hw n => ?_⟩
    set S : Strat M := ⟨fun l => cell hM hr (l.headD 0), fun l => match l with
      | [] => 0
      | m :: _ => -(a * centre M r m)⟩ with hSdef
    have hm : ∀ n, ∃ t, (hist a S x₀ w n).2 = cell hM hr (st a S x₀ w n) :: t := by
      intro n; cases n with
      | zero => exact ⟨[], rfl⟩
      | succ n => exact ⟨_, rfl⟩
    induction n with
    | zero => simpa [st, hist] using hx
    | succ n ih =>
      obtain ⟨t, ht⟩ := hm n
      have e : st a S x₀ w (n + 1) = a * st a S x₀ w n +
          -(a * centre M r (cell hM hr (st a S x₀ w n))) + w n := by
        show a * st a S x₀ w n + S.act (hist a S x₀ w n).2 + w n = _
        rw [ht]
      rw [e]; exact cell_safe hM hr h ih (hw n)

/-- The threshold as a number of messages. -/
theorem messages_iff (hM : 0 < M) (hr : 0 < r) (hd : 0 ≤ d) (hdr : d < r) :
    (∃ S : Strat M, Viable a r d S) ↔ |a| * r / (r - d) ≤ M := by
  rw [forever_iff hM hr hd, div_le_iff₀ (by linarith)]
  constructor <;> intro h <;> linarith

/-- The threshold in bits per step. -/
theorem bits_forever_iff (b : ℕ) (hr : 0 < r) (hd : 0 ≤ d) :
    (∃ S : Strat (2 ^ b), Viable a r d S) ↔ |a| * r ≤ 2 ^ b * (r - d) := by
  rw [forever_iff (by positivity) hr hd]; push_cast
  constructor <;> intro h <;> linarith

/-- With one message (no information) and `|a| ≥ 1`, `d > 0`, nothing survives. -/
theorem blind_dies (hr : 0 < r) (hd : 0 < d) (ha : 1 ≤ |a|) :
    ¬ ∃ S : Strat 1, Viable a r d S := by
  rw [forever_iff one_pos hr hd.le]; push_cast; nlinarith

/-! ### Continuous reading with bounded error -/

/-- **A memoryless rule on a reading with error `≤ s` is safe iff `|a| s + d ≤ r`.** -/
theorem sensor_error_iff (hd : 0 ≤ d) (hs : 0 ≤ s) (hsr : s ≤ r) :
    (∃ π : ℝ → ℝ, ∀ x, |x| ≤ r → ∀ e, |e| ≤ s → ∀ w, |w| ≤ d →
      |a * x + π (x + e) + w| ≤ r) ↔ |a| * s + d ≤ r := by
  constructor
  · rintro ⟨π, h⟩
    have hs' : |s| ≤ s := by rw [abs_of_nonneg hs]
    have hs'' : |-s| ≤ s := by rw [abs_neg]; exact hs'
    have hd' : |d| ≤ d := by rw [abs_of_nonneg hd]
    have hd'' : |-d| ≤ d := by rw [abs_neg]; exact hd'
    have p1 := abs_le.1 (h s (hs'.trans hsr) (-s) hs'' d hd')
    have p2 := abs_le.1 (h s (hs'.trans hsr) (-s) hs'' (-d) hd'')
    have p3 := abs_le.1 (h (-s) (hs''.trans hsr) s hs' d hd')
    have p4 := abs_le.1 (h (-s) (hs''.trans hsr) s hs' (-d) hd'')
    simp only [add_neg_cancel, neg_add_cancel] at p1 p2 p3 p4
    rcases abs_cases a with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> nlinarith
  · intro h
    refine ⟨fun y => -(a * y), fun x _ e he w hw => ?_⟩
    have : a * x + -(a * (x + e)) + w = -(a * e) + w := by ring
    rw [this]
    calc _ ≤ |-(a * e)| + |w| := abs_add_le _ _
      _ ≤ |a| * s + d := by
        rw [abs_neg, abs_mul]; exact add_le_add (mul_le_mul_of_nonneg_left he (abs_nonneg a)) hw
      _ ≤ r := h

/-- The critical sensor error is `(r − d)/|a|`. -/
theorem critical_error (ha : a ≠ 0) (hd : 0 ≤ d) (hs : 0 ≤ s) (hsr : s ≤ r) :
    (∃ π : ℝ → ℝ, ∀ x, |x| ≤ r → ∀ e, |e| ≤ s → ∀ w, |w| ≤ d →
      |a * x + π (x + e) + w| ≤ r) ↔ s ≤ (r - d) / |a| := by
  rw [sensor_error_iff hd hs hsr, le_div_iff₀ (abs_pos.2 ha)]
  constructor <;> intro h <;> linarith

end FiveOrgans.SensingRate
