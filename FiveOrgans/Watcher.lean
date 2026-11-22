import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The Watcher: when does a checker help?

Model (binary decision, one check).
* `p` — probability the base system ("narrator") is right.
* `α` — false-alarm rate: the Watcher flags a *correct* answer.
* `β` — detection rate: the Watcher flags a *wrong* answer.
* A flagged answer is flipped (two actions, so flipping a wrong answer fixes it
  and flipping a right one breaks it).
* `c` — cost of running the check, in accuracy units.

Accuracy after one check: `p(1-α) + (1-p)β`.

Results.
* `gain_eq`            — gain = `(1-p)β − pα`.
* `helps_iff`          — the Watcher pays for itself iff `(1-p)β − pα > c`.
* `helps_iff_threshold`— with no cost: helps iff `p(α+β) < β`, i.e. the base is
                         below the threshold `β/(α+β)`. A stronger narrator
                         needs a better Watcher.
* `sham_hurts`         — a sham Watcher (flags independent of correctness,
                         α = β) strictly hurts any better-than-chance base.
* `forced_check_formula`, `forced_check_tendsto` — checking the same answer
  every step with independent errors drives accuracy to `β/(α+β)` whatever the
  base accuracy was: forced checking erases the base's competence.

Empirical links (see ASSUMPTIONS.md): Witnessed Introspection (ledger lowered
accuracy), forced-check −0.146 with 11/12 seeds on a constant floor, sham
Watcher null.
-/

namespace FiveOrgans.Watcher

/-- Accuracy after one flip-on-flag check. -/
def acc (p α β : ℝ) : ℝ := p * (1 - α) + (1 - p) * β

theorem gain_eq (p α β : ℝ) : acc p α β - p = (1 - p) * β - p * α := by
  unfold acc; ring

/-- The Watcher is worth its cost iff detection-weighted gain beats false-alarm
loss by more than the cost. -/
theorem helps_iff (p α β c : ℝ) :
    acc p α β - c > p ↔ (1 - p) * β - p * α > c := by
  have := gain_eq p α β
  constructor <;> intro h <;> linarith

/-- Cost-free threshold form. -/
theorem helps_iff_threshold (p α β : ℝ) :
    acc p α β > p ↔ p * (α + β) < β := by
  have := gain_eq p α β
  constructor <;> intro h <;> nlinarith

/-- A sham Watcher flags at rate `f` regardless of correctness. Against any base
that is better than chance, it strictly lowers accuracy. -/
theorem sham_hurts {p f : ℝ} (hp : 1 / 2 < p) (hf : 0 < f) :
    acc p f f < p := by
  have := gain_eq p f f
  nlinarith

/-- Accuracy after `n` independent checks of the same answer. -/
def accN (α β p : ℝ) : ℕ → ℝ
  | 0 => p
  | n + 1 => acc (accN α β p n) α β

/-- Closed form: the gap to the fixed point `β/(α+β)` shrinks by `(1-α-β)`
each round. -/
theorem forced_check_formula {α β : ℝ} (hab : α + β ≠ 0) (p : ℝ) (n : ℕ) :
    accN α β p n = β / (α + β) + (1 - α - β) ^ n * (p - β / (α + β)) := by
  induction n with
  | zero => simp [accN]
  | succ n ih =>
    rw [accN, ih, acc, pow_succ]
    field_simp
    ring

/-- Forced checking converges to `β/(α+β)`, independent of the starting
accuracy `p`. -/
theorem forced_check_tendsto {α β : ℝ} (hab : 0 < α + β) (hab2 : α + β < 2) (p : ℝ) :
    Filter.Tendsto (accN α β p) Filter.atTop (nhds (β / (α + β))) := by
  have hr : |1 - α - β| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  have h0 := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr
  have h1 := (h0.mul_const (p - β / (α + β))).const_add (β / (α + β))
  simp only [zero_mul, add_zero] at h1
  refine h1.congr (fun n => ?_)
  rw [forced_check_formula (ne_of_gt hab)]

end FiveOrgans.Watcher
