import FiveOrgans.TwoSpeed
import FiveOrgans.ViabilityStochastic

/-!
# Two-speed × Viability: one rate dies, two rates survive

Each episode the environment poses both demands from `TwoSpeed`: a step change to be caught
within `N` steps (lag `(1-η)^N ≤ ε`) and alternating noise `±σ` to be ridden out (ripple
`ησ/(2-η) ≤ δ`). An unmet demand costs hazard `c` that episode.

* `single_rate_dies` — under the conflict condition of `single_rate_conflict`, every single rate
  `η ∈ [0,1]` leaves some demand unmet in every episode, so the hazard is the constant `c`
  and survival goes to 0.
* `two_rates_survive` — a fast trace (`η = 1`) meets the change demand and a slow trace
  (`η = 2δ/(σ+δ)`) meets the noise demand. The hazard is 0 and survival is 1 forever.
* `two_speed_instance` — non-vacuous: σ = 1, δ = 1/100, N = 10, ε = 1/2, c = 1/100.

Honest scope: the survival step is thin. The hazard is defined as "c when a demand is unmet",
so the substance is `single_rate_conflict` and this file only turns it into a viability
statement. It assumes (EMP?) that the environment really poses both demands in every episode
and that an unmet demand carries a fixed hazard. A world that poses only one demand does not
need two speeds.
-/

namespace FiveOrgans.TwoSpeedViability
open FiveOrgans.ViabilityStochastic

/-- Both demands met by the (change-trace rate, noise-trace rate) pair. -/
def Meets (σ δ ε : ℝ) (N : ℕ) (ηf ηs : ℝ) : Prop :=
  (1 - ηf) ^ N ≤ ε ∧ ηs * σ / (2 - ηs) ≤ δ

open Classical in
/-- Per-episode hazard: `c` if a demand is unmet, else 0. -/
noncomputable def hz (c σ δ ε : ℝ) (N : ℕ) (ηf ηs : ℝ) (_ : ℕ) : ℝ :=
  if Meets σ δ ε N ηf ηs then 0 else c

/-- **One rate for both jobs: survival → 0.** -/
theorem single_rate_dies {c σ δ ε : ℝ} {N : ℕ} (hσ : 0 ≤ σ) (hδ : 0 < δ) (hδσ : δ ≤ σ)
    (hslow : ε < (1 - 2 * δ / (σ + δ)) ^ N) {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1)
    (hc0 : 0 < c) (hc1 : c ≤ 1) {ε' : ℝ} (hε' : ε' < 1) :
    ∃ n, surv (hz c σ δ ε N η η) n < 1 - ε' := by
  have hno : ¬ Meets σ δ ε N η η := TwoSpeed.single_rate_conflict hσ hδ hδσ hslow h0 h1
  have : hz c σ δ ε N η η = fun _ => c := by funext i; simp [hz, hno]
  rw [this]
  exact const_hazard_dies hc0 hc1 hε'

/-- **A fast and a slow trace: survival 1 forever.** -/
theorem two_rates_survive {c σ δ ε : ℝ} {N : ℕ} (hN : 1 ≤ N) (hε : 0 ≤ ε) (hσ : 0 ≤ σ)
    (hδ : 0 < δ) (hδσ : δ ≤ σ) (n : ℕ) :
    surv (hz c σ δ ε N 1 (2 * δ / (σ + δ))) n = 1 := by
  have hyes : Meets σ δ ε N 1 (2 * δ / (σ + δ)) := TwoSpeed.two_rates_suffice hN hε hσ hδ hδσ
  unfold surv
  simp [hz, hyes]

/-- Non-vacuity: σ = 1, δ = 1/100, N = 10, ε = 1/2, c = 1/100. Every single rate in `[0,1]`
eventually falls below survival 1/2; the two-trace agent never fails. -/
theorem two_speed_instance :
    (∀ η : ℝ, 0 ≤ η → η ≤ 1 →
      ∃ n, surv (hz (1 / 100) 1 (1 / 100) (1 / 2) 10 η η) n < 1 / 2) ∧
    ∀ n, surv (hz (1 / 100) 1 (1 / 100) (1 / 2) 10 1 (2 * (1 / 100) / (1 + 1 / 100))) n = 1 := by
  refine ⟨fun η h0 h1 => ?_, fun n => two_rates_survive (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) n⟩
  obtain ⟨n, hn⟩ := single_rate_dies (c := 1 / 100) (σ := 1) (δ := 1 / 100) (ε := 1 / 2) (N := 10)
    (ε' := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) h0 h1 (by norm_num) (by norm_num) (by norm_num)
  exact ⟨n, by linarith⟩

end FiveOrgans.TwoSpeedViability
