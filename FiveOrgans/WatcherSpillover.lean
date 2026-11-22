import FiveOrgans.WatcherCompliance

/-!
# Watcher with compliance and spillover

Four cells, by base answer (right w.p. `p`) and flag (`α` if right, `β` if wrong):
* right, unflagged `p(1-α)`: flips (spillover, prob `s`) → wrong;
* wrong, unflagged `(1-p)(1-β)`: flips w.p. `s` → right (binary answers);
* right, flagged `pα`: complies w.p. `q` → right iff ledger right (`r₁`); else stays right;
* wrong, flagged `(1-p)β`: complies w.p. `q` → right w.p. `r₀`; else stays wrong.

Results.
* `gainQS_eq` — gain `= q·G + s·((1-p)(1-β) - p(1-α))`.
* `no_spill_is_compliance` — at `s = 0` this is exactly `WatcherCompliance.accQ`.
* `perfect_watcher_spill` — perfect Watcher (`α=0, β=1, r₀=1`): gain `= q(1-p) - s·p`.
  Spillover costs exactly `s·p`: it only hurts, because every unflagged probe was right.

Motivation (S126 v5, memory framing, post hoc): `p = 2/3`, `q = 0.72`, `s = 6/64`;
predicted `q/3 - (2/3)s`; the observed residual vs `q·G` was `-0.0625 = -(2/3)(6/64)`.
-/

namespace FiveOrgans.WatcherSpillover
open FiveOrgans.WatcherFallback FiveOrgans.WatcherCompliance

def accQS (p α β r₁ r₀ q s : ℝ) : ℝ :=
  p * (1 - α) * (1 - s) + (1 - p) * (1 - β) * s
    + p * α * (q * r₁ + (1 - q)) + (1 - p) * β * (q * r₀)

theorem gainQS_eq (p α β r₁ r₀ q s : ℝ) :
    accQS p α β r₁ r₀ q s - p
      = q * ((1 - p) * β * r₀ - p * α * (1 - r₁))
        + s * ((1 - p) * (1 - β) - p * (1 - α)) := by
  unfold accQS; ring

theorem no_spill_is_compliance (p α β r₁ r₀ q : ℝ) :
    accQS p α β r₁ r₀ q 0 = accQ p α β r₁ r₀ q := by
  have h1 := gainQS_eq p α β r₁ r₀ q 0
  have h2 := gainQ_eq p α β r₁ r₀ q
  linarith

theorem perfect_watcher_spill (p r₁ q s : ℝ) :
    accQS p 0 1 r₁ 1 q s - p = q * (1 - p) - s * p := by
  rw [gainQS_eq]; ring

/-- **Adversarial Watcher** (the record always implies the wrong answer): it flags exactly the
right answers (`α = 1, β = 0`) and every flag points wrong (`r₁ = 0`). Then `G = -p`, and
gain `= -q·p + s·(1-p)`: deference costs `q·p`, and spillover can only help here. -/
theorem adversarial_watcher (p r₀ q s : ℝ) :
    accQS p 1 0 0 r₀ q s - p = -(q * p) + s * (1 - p) := by
  rw [gainQS_eq]; ring

/-- Under an adversarial Watcher with no spillover, full deference (`q = 1`) drives accuracy
to zero: `accQS = (1 - q) p`. -/
theorem adversarial_full_defer (p r₀ q : ℝ) : accQS p 1 0 0 r₀ q 0 = (1 - q) * p := by
  unfold accQS; ring

end FiveOrgans.WatcherSpillover
