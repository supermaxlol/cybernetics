import FiveOrgans.Memory
import FiveOrgans.Watcher
import FiveOrgans.WatcherCompliance
import FiveOrgans.Brake
import FiveOrgans.BrakeDelayUnstable
import FiveOrgans.Spotlight
import FiveOrgans.Skin
import FiveOrgans.TwoSpeed
import FiveOrgans.Viability
import FiveOrgans.ViabilityStochastic

/-!
# What the library licenses, stated as two theorems on concrete instances

Both are conjunctions of earlier results instantiated at concrete numbers, so each clause
is *non-vacuous*: the failure really occurs in at least one fully specified world.
They are **existence** claims about toy models, not frequency claims about real agents.

* `absence_fails` — for each function, a world where the agent *lacking* it fails:
  no memory (two histories look the same but need different actions), no brake (gain 3
  diverges), one speed (no single EMA rate meets both demands), myopic choice (best-now
  loses by step 3 and exits `K`), constant hazard (survival → 0).
* `misconfigured_worse_than_absent` — for three organs, a world where the organ *set
  wrong* is strictly worse than having none: a sham Watcher lowers accuracy below the
  base rate; a misdirected Spotlight does worse than an even spread; an over-strong Brake
  diverges where no brake at all stays bounded. Add the delay result: a brake gain that
  is safe with no delay is unsafe with any delay.

NOT claimed: that these five are jointly sufficient, that there are exactly five, or that any
real system instantiates these models. Those are the open joint theorem and cross-scale map.
-/

namespace FiveOrgans.Claims

theorem absence_fails :
    -- memory: two histories with the same observation and no shared safe action
    (¬ ∃ π : Unit → Bool,
        Memory.SafeAgent (fun (h : Bool) (a : Bool) => a = h) (fun _ => ()) π) ∧
    -- brake: gain 3 with no brake diverges
    (¬ ∃ B, ∀ n, |Brake.traj 3 0 1 n| ≤ B) ∧
    -- one speed: no EMA rate reaches error ≤ 1/2 in 10 steps with ripple ≤ 1/100
    (∀ η : ℝ, 0 ≤ η → η ≤ 1 → ¬ ((1 - η) ^ 10 ≤ 1 / 2 ∧ η * 1 / (2 - η) ≤ 1 / 100)) ∧
    -- myopia: exploiting is best this step, yet loses over 3 steps
    (Viability.reward true true > Viability.reward true false ∧
      Viability.total Viability.exploit 3 true < Viability.total Viability.sustain 3 true) ∧
    -- constant hazard 1/100: survival eventually below 1/2
    (∃ n, ViabilityStochastic.surv (fun _ => (1 : ℝ) / 100) n < 1 / 2) := by
  refine ⟨?_, ?_, fun η h0 h1 => TwoSpeed.conflict_instance η h0 h1,
    ⟨Viability.myopic_prefers_exploit, Viability.sustain_beats_exploit 3 le_rfl⟩, ?_⟩
  · exact Memory.memoryless_fails _ _ (h₁ := true) (h₂ := false) rfl
      (fun a h1 h2 => by rw [h1] at h2; exact Bool.noConfusion h2)
  · rw [Brake.window_iff one_ne_zero]; norm_num
  · obtain ⟨n, hn⟩ := ViabilityStochastic.const_hazard_dies (c := 1 / 100) (ε := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
    exact ⟨n, by linarith⟩

theorem misconfigured_worse_than_absent :
    -- sham Watcher (α = β = 1/2) on a base right 3/4 of the time: below 3/4
    Watcher.acc (3 / 4) (1 / 2) (1 / 2) < 3 / 4 ∧
    -- spotlight on the irrelevant item: worse than an even spread
    Spotlight.payoff (Spotlight.spot 1 (1 : Fin 2)) ![1, 0]
      < Spotlight.payoff (Spotlight.uniform 1 2) ![1, 0] ∧
    -- gain 1: no brake stays bounded, brake 3 diverges
    ((∃ B, ∀ n, |Brake.traj 1 0 1 n| ≤ B) ∧ ¬ ∃ B, ∀ n, |Brake.traj 1 3 1 n| ≤ B) ∧
    -- delay: brake gain 3/2 safe undelayed, unsafe with a one-step delay
    ((∀ x : ℕ → ℝ, (∀ n, x (n + 1) = (1 - 3 / 2) * x n) → ∀ n, |x n| ≤ |x 0|) ∧
      ∃ x : ℕ → ℝ, (∀ n, x (n + 1 + 1) = x (n + 1) - 3 / 2 * x n) ∧ ∀ B, ∃ n, B < |x n|) := by
  refine ⟨Watcher.sham_hurts (by norm_num) (by norm_num), ?_, ⟨?_, ?_⟩,
    BrakeDelayUnstable.delay_caps_gain (d := 1) le_rfl (by norm_num) (by norm_num)⟩
  · exact Spotlight.misdirected_spotlight one_pos (by norm_num) (by simp [Fin.sum_univ_two])
  · rw [Brake.window_iff one_ne_zero]; norm_num
  · rw [Brake.window_iff one_ne_zero]; norm_num

end FiveOrgans.Claims
