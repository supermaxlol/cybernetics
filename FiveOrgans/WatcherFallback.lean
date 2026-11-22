import FiveOrgans.Watcher

/-!
# The Watcher with a fallback ("defer when flagged")

The base answer is right with probability `p`. The Watcher flags a right answer with
probability `α` (false alarm) and a wrong one with probability `β` (detection).
A flagged answer is **replaced by a fallback**, which is right with probability `r₁`
on items the base got right and `r₀` on items the base got wrong.

  `accF = p(1-α) + pα·r₁ + (1-p)β·r₀`

Results.
* `gainF_eq`, `fallback_helps_iff` — gain `= (1-p)β r₀ - pα(1-r₁)`.
* `flip_special_case` — binary flipping (`Watcher.acc`) is `r₁ = 0, r₀ = 1`.
* `independent_helps_iff` — with an item-independent fallback (`r₁ = r₀ = r`),
  deferring helps iff `r > pα / (pα + (1-p)β)`, i.e. iff the fallback beats the base's
  own accuracy **on the flagged items**.
* `always_flag_constant` — a Watcher that flags everything (`α = β = 1`) gives accuracy
  exactly `r`, whatever `p` is. This is the S126 forced-check pattern: all 12 seeds sat
  at the always-"no" floor 8/12 regardless of base skill (notes/05).
* `sham_fallback_gain` — an uninformative Watcher (`α = β = f`) changes accuracy by
  `f (r - p)`: it only helps when the fallback is better than the base anyway.
-/

namespace FiveOrgans.WatcherFallback

/-- Accuracy with defer-to-fallback on flag. -/
def accF (p α β r₁ r₀ : ℝ) : ℝ := p * (1 - α) + p * α * r₁ + (1 - p) * β * r₀

theorem gainF_eq (p α β r₁ r₀ : ℝ) :
    accF p α β r₁ r₀ - p = (1 - p) * β * r₀ - p * α * (1 - r₁) := by
  unfold accF; ring

theorem fallback_helps_iff (p α β r₁ r₀ c : ℝ) :
    p + c < accF p α β r₁ r₀ ↔ p * α * (1 - r₁) + c < (1 - p) * β * r₀ := by
  have := gainF_eq p α β r₁ r₀
  constructor <;> intro h <;> linarith

/-- Flipping a binary answer = a fallback that is always wrong when the base was right
and always right when the base was wrong. -/
theorem flip_special_case (p α β : ℝ) : accF p α β 0 1 = Watcher.acc p α β := by
  unfold accF Watcher.acc; ring

theorem independent_gain (p α β r : ℝ) :
    accF p α β r r - p = r * (p * α + (1 - p) * β) - p * α := by
  unfold accF; ring

/-- Defer only if the fallback beats the base's accuracy on flagged items. -/
theorem independent_helps_iff {p α β : ℝ} (hF : 0 < p * α + (1 - p) * β) (r : ℝ) :
    p < accF p α β r r ↔ p * α / (p * α + (1 - p) * β) < r := by
  rw [div_lt_iff₀ hF]
  have := independent_gain p α β r
  constructor <;> intro h <;> nlinarith

/-- Flag-everything Watcher: accuracy is the fallback's, independent of base skill. -/
theorem always_flag_constant (p r : ℝ) : accF p 1 1 r r = r := by
  unfold accF; ring

/-- Uninformative Watcher with an independent fallback. -/
theorem sham_fallback_gain (p f r : ℝ) : accF p f f r r - p = f * (r - p) := by
  unfold accF; ring

theorem sham_fallback_hurts {p f r : ℝ} (hf : 0 < f) (hr : r < p) : accF p f f r r < p := by
  have := sham_fallback_gain p f r
  nlinarith

end FiveOrgans.WatcherFallback
