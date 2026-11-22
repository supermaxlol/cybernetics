import FiveOrgans.Watcher

/-!
# Discerning compliance: obeying right flags and wrong flags at different rates

S126 v6 (notes/08) refuted the constant-compliance assumption whenever the record could be checked
against context: the model followed 42% of correct flags and 0% of wrong ones. This module
generalises the Watcher model to two compliance rates.

Binary answers. The base is right with probability `p`. The Watcher flags a right answer with
probability `α` (a wrong flag) and a wrong answer with probability `β` (a correct flag). The agent
switches its answer on a correct flag with probability `q₊`, and on a wrong flag with
probability `q₋`.

  `acc2 = p (1 - α q₋) + (1 - p) β q₊`,   `gain = q₊ (1-p) β - q₋ p α`  (`gain2_eq`).

* `constant_q` — with `q₊ = q₋ = q` this is `q · (acc - p)`: the old law.
* `undiscerning_sham_hurts` — with constant `q > 0` a sham Watcher (`α = β = f > 0`) hurts when `p > 1/2`.
* `discerning_never_hurts` — if wrong flags are ignored (`q₋ = 0`), **any** Watcher, even a sham
  or an always-wrong one, has gain `≥ 0`.
* `helps_iff_discernment` — a sham Watcher (`α = β = f > 0`) helps iff `q₊ (1-p) > q₋ p`, i.e. the
  agent's discernment ratio `q₊/q₋` beats the base odds `p/(1-p)`.
* `adversarial_discerning` — always-wrong ledger (`α = 1, β = 0`): gain `= -q₋ p`, which is zero
  iff `q₋ = 0` (for `p > 0`). This matches the v6 sham-authority arm on the flagged items.

Reading: the danger of a bad Watcher lies in the agent's indiscriminate obedience, not in the
Watcher alone. Discernment, meaning the ability to tell right flags from wrong ones, is what
makes it safe to listen. Where does `q₋ ≈ 0` come from? In v6 it plausibly came from checking
against the history in context. That is a hypothesis (EMP?), not something this module proves.
-/

namespace FiveOrgans.WatcherDiscerning

/-- Accuracy with discerning compliance. -/
def acc2 (p α β qp qm : ℝ) : ℝ := p * (1 - α * qm) + (1 - p) * β * qp

theorem gain2_eq (p α β qp qm : ℝ) :
    acc2 p α β qp qm - p = qp * (1 - p) * β - qm * p * α := by
  unfold acc2; ring

/-- Equal rates recover the constant-compliance law `gain = q · G`. -/
theorem constant_q (p α β q : ℝ) : acc2 p α β q q - p = q * (Watcher.acc p α β - p) := by
  unfold acc2 Watcher.acc; ring

/-- Undiscerning (equal rates) obedience to a sham Watcher hurts a better-than-chance base. -/
theorem undiscerning_sham_hurts {p f q : ℝ} (hp : 1 / 2 < p) (hf : 0 < f) (hq : 0 < q) :
    acc2 p f f q q < p := by
  have h := constant_q p f f q
  have hs := Watcher.sham_hurts hp hf
  nlinarith

/-- **Ignoring wrong flags makes every Watcher harmless.** -/
theorem discerning_never_hurts {p α β qp : ℝ} (hp1 : p ≤ 1) (hβ : 0 ≤ β)
    (hqp : 0 ≤ qp) : p ≤ acc2 p α β qp 0 := by
  have := gain2_eq p α β qp 0
  have : 0 ≤ qp * (1 - p) * β := mul_nonneg (mul_nonneg hqp (by linarith)) hβ
  linarith

/-- **A sham Watcher helps iff discernment beats the base odds.** -/
theorem helps_iff_discernment {p f qp qm : ℝ} (hf : 0 < f) :
    p < acc2 p f f qp qm ↔ qm * p < qp * (1 - p) := by
  have h := gain2_eq p f f qp qm
  constructor
  · intro hlt
    have : 0 < (qp * (1 - p) - qm * p) * f := by nlinarith
    exact by nlinarith [(pos_iff_pos_of_mul_pos this).mpr hf]
  · intro hlt
    have : 0 < (qp * (1 - p) - qm * p) * f := mul_pos (by linarith) hf
    nlinarith

/-- **Always-wrong ledger:** the cost is exactly `q₋ p`. -/
theorem adversarial_discerning (p qp qm : ℝ) : acc2 p 1 0 qp qm - p = -(qm * p) := by
  unfold acc2; ring

theorem adversarial_harmless_iff {p qp qm : ℝ} (hp : 0 < p) :
    acc2 p 1 0 qp qm = p ↔ qm = 0 := by
  have := adversarial_discerning p qp qm
  constructor
  · intro h
    have : qm * p = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  · intro h; subst h; linarith

/-- v6 numbers on flagged items (`notes/08`): base `p = 65/96`. True record (`α = 0, β = 1`) with
`q₊ = 13/31` gives gain `13/96`; the always-wrong record (`α = 1, β = 0`) with `q₋ = 0` gives
gain 0. -/
theorem v6_instance :
    acc2 (65 / 96) 0 1 (13 / 31) 0 - 65 / 96 = 13 / 96 ∧ acc2 (65 / 96) 1 0 0 0 = 65 / 96 := by
  constructor <;> (unfold acc2; norm_num)

end FiveOrgans.WatcherDiscerning
