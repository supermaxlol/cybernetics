import FiveOrgans.WatcherFallback
import Mathlib.Tactic.LinearCombination

/-!
# Watcher with partial compliance

`WatcherFallback.accF` assumes a flagged answer is always replaced. Real agents may
ignore the flag. With compliance `q ∈ [0,1]` (probability the agent acts on a flag):

  `accQ = (1 - q) · p + q · accF`.

Results.
* `gainQ_eq` — the realised gain is exactly `q · G`, where `G` is the full-compliance
  gain `(1-p)β r₀ - pα(1-r₁)` (`WatcherFallback.gainF_eq`).
* `perfect_watcher_gain` — a perfect Watcher (`α = 0`, `β = 1`, `r₀ = 1`) is worth exactly
  `q · (1 - p)`.
* `ignored_watcher_useless` — at `q = 0` every Watcher, however accurate, has zero effect.
* `gain_monotone_in_q` — for a helpful Watcher (`G > 0`) more compliance is strictly better.

Motivation (S126 v4, Groq gpt-oss-120b, 2026-11-21): the ledger was perfect on the
check arm (α = 0, β = 1, r₀ = 1, so G = 1 - p = 1/3) yet the model answered against it on
every flagged probe (q = 0), so the observed gain was 0 — exactly `q · G`. Detection
was not the bottleneck; acting on the detection was.
-/

namespace FiveOrgans.WatcherCompliance
open FiveOrgans.WatcherFallback

def accQ (p α β r₁ r₀ q : ℝ) : ℝ := (1 - q) * p + q * accF p α β r₁ r₀

theorem gainQ_eq (p α β r₁ r₀ q : ℝ) :
    accQ p α β r₁ r₀ q - p = q * ((1 - p) * β * r₀ - p * α * (1 - r₁)) := by
  unfold accQ
  have := gainF_eq p α β r₁ r₀
  linear_combination q * this

theorem perfect_watcher_gain (p r₁ q : ℝ) : accQ p 0 1 r₁ 1 q - p = q * (1 - p) := by
  rw [gainQ_eq]; ring

theorem ignored_watcher_useless (p α β r₁ r₀ : ℝ) : accQ p α β r₁ r₀ 0 = p := by
  unfold accQ; ring

theorem gain_monotone_in_q {p α β r₁ r₀ q q' : ℝ}
    (hG : 0 < (1 - p) * β * r₀ - p * α * (1 - r₁)) (hq : q < q') :
    accQ p α β r₁ r₀ q < accQ p α β r₁ r₀ q' := by
  have h1 := gainQ_eq p α β r₁ r₀ q
  have h2 := gainQ_eq p α β r₁ r₀ q'
  nlinarith [mul_lt_mul_of_pos_right hq hG]

end FiveOrgans.WatcherCompliance
