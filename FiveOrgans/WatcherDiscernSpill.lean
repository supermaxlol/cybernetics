import FiveOrgans.WatcherDiscerning

/-!
# Discerning Watcher with spillover: doubt that leaks onto records the checker did not flag

`WatcherSpillover` added spillover to the constant-compliance model. Here it is added to
the discerning one. `WatcherDiscerning.acc2` assumes the agent only changes answers the checker flags. v6 refuted
this for the sham arm under authority framing: q₋ = 0/65 (no wrong flag obeyed), yet accuracy
*rose* by 5/96, because the agent also flipped 5 of its 31 **unflagged** answers. `acc2`
predicts gain 0 there (`adversarial_discerning` with q₋ = 0).

Add a **spillover** rate `s`: each unflagged answer is flipped with probability `s`.

  `acc3 = p(1-α)(1-s) + pα(1-q₋) + (1-p)β q₊ + (1-p)(1-β) s`.

* `acc3_eq` — `acc3 = acc2 + s·[(1-p)(1-β) − p(1-α)]`: spillover helps iff the unflagged pool
  holds more wrong answers than right ones.
* `adversarial_spill` — always-wrong checker (α = 1, β = 0): gain `= s(1-p) − q₋ p`. Every
  unflagged answer is a wrong one, so doubt there can only help.
* `sham_helps_iff` — a sham checker raises accuracy iff `q₋ p < s (1-p)`.
* `honest_spill` — always-right checker (α = 0, β = 1): gain `= q₊(1-p) − s p`. The same doubt
  now costs, because every unflagged answer is a right one.
* `spill_tradeoff` — so no `s > 0` is free: for `0 < p < 1` it helps under the sham checker and
  hurts under the honest one, by amounts that add to `s`.
* `v6_sham_instance` — p = 65/96, q₋ = 0, s = 5/31 gives gain exactly 5/96, the observed v6
  sham-authority gain.

Interpretation (EMP?): spillover is undirected doubt. It is a weak Watcher that improves
accuracy only where the unflagged answers are mostly wrong. Scope: s is the same for right and
wrong unflagged answers. v6 cannot test that: in the sham arm every unflagged answer was wrong.
-/

namespace FiveOrgans.WatcherDiscernSpill
open FiveOrgans.WatcherDiscerning

/-- Accuracy with flag compliance `qp`/`qm` and spillover `s` on unflagged answers. -/
def acc3 (p α β qp qm s : ℝ) : ℝ :=
  p * (1 - α) * (1 - s) + p * α * (1 - qm) + (1 - p) * β * qp + (1 - p) * (1 - β) * s

theorem acc3_eq (p α β qp qm s : ℝ) :
    acc3 p α β qp qm s = acc2 p α β qp qm + s * ((1 - p) * (1 - β) - p * (1 - α)) := by
  unfold acc3 acc2; ring

theorem acc3_no_spill (p α β qp qm : ℝ) : acc3 p α β qp qm 0 = acc2 p α β qp qm := by
  rw [acc3_eq]; ring

/-- Spillover helps iff the unflagged pool is mostly wrong. -/
theorem spill_helps_iff {p α β qp qm s : ℝ} (hs : 0 < s) :
    acc2 p α β qp qm < acc3 p α β qp qm s ↔ p * (1 - α) < (1 - p) * (1 - β) := by
  rw [acc3_eq]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Always-wrong checker:** gain `= s(1-p) − q₋ p`. -/
theorem adversarial_spill (p qp qm s : ℝ) : acc3 p 1 0 qp qm s - p = s * (1 - p) - qm * p := by
  unfold acc3; ring

/-- A sham checker raises accuracy iff `q₋ p < s(1-p)`. -/
theorem sham_helps_iff {p qp qm s : ℝ} : p < acc3 p 1 0 qp qm s ↔ qm * p < s * (1 - p) := by
  have := adversarial_spill p qp qm s
  constructor <;> intro h <;> linarith

/-- **Always-right checker:** gain `= q₊(1-p) − s p`. -/
theorem honest_spill (p qp qm s : ℝ) : acc3 p 0 1 qp qm s - p = qp * (1 - p) - s * p := by
  unfold acc3; ring

/-- **No free doubt:** the spillover term is `+s(1-p)` under the sham checker and `−s p` under
the honest one. Both are nonzero when `0 < s` and `0 < p < 1`, and they differ by exactly `s`. -/
theorem spill_tradeoff {p qp qm s : ℝ} (hs : 0 < s) (hp0 : 0 < p) (hp1 : p < 1) :
    (acc3 p 1 0 qp qm s - acc3 p 1 0 qp qm 0) > 0 ∧
    (acc3 p 0 1 qp qm s - acc3 p 0 1 qp qm 0) < 0 ∧
    (acc3 p 1 0 qp qm s - acc3 p 1 0 qp qm 0) - (acc3 p 0 1 qp qm s - acc3 p 0 1 qp qm 0) = s := by
  unfold acc3
  refine ⟨by nlinarith, by nlinarith, by ring⟩

/-- **v6 sham-authority arm:** 65/96 right at base, 0/65 wrong flags obeyed, 5/31 unflagged
answers flipped ⇒ gain exactly 5/96, as observed. `acc2` alone predicts 0. -/
theorem v6_sham_instance :
    acc3 (65 / 96) 1 0 0 0 (5 / 31) - 65 / 96 = 5 / 96 ∧
    acc2 (65 / 96) 1 0 0 0 - 65 / 96 = 0 := by
  constructor <;> norm_num [acc3, acc2]

/-- **All four v6 arms, exactly** (p = 65/96; 31 wrong and 65 right base answers):
* ver_sys   (α=0, β=1): q₊ = 1/31, s = 1/65 ⇒ gain 0;
* ver_auth  (α=0, β=1): q₊ = 13/31, s = 0   ⇒ gain 13/96;
* sham_sys  (α=1, β=0): q₋ = 1/65, s = 1/31 ⇒ gain 0;
* sham_auth (α=1, β=0): q₋ = 0, s = 5/31    ⇒ gain 5/96.
These are the observed gains. They are accounting identities, not predictions: given the
measured rates, the model's four terms account for every answer change. -/
theorem v6_all_arms :
    acc3 (65 / 96) 0 1 (1 / 31) 0 (1 / 65) - 65 / 96 = 0 ∧
    acc3 (65 / 96) 0 1 (13 / 31) 0 0 - 65 / 96 = 13 / 96 ∧
    acc3 (65 / 96) 1 0 0 (1 / 65) (1 / 31) - 65 / 96 = 0 ∧
    acc3 (65 / 96) 1 0 0 0 (5 / 31) - 65 / 96 = 5 / 96 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [acc3]

end FiveOrgans.WatcherDiscernSpill
