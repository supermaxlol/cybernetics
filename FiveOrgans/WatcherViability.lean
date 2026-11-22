import FiveOrgans.WatcherCompliance
import FiveOrgans.BrakeViability

/-!
# Watcher × Viability: a static Watcher delays death but cannot prevent it

Read each step as one decision that fails with hazard `1 - accuracy`. A Watcher that is obeyed and
better than chance raises accuracy from `p` to `accQ p α β r₁ r₀ q`, which lowers the hazard.

* `watcher_lowers_hazard` — if the realised gain `accQ - p` is positive, the per-step hazard is
  strictly below the unwatched `1 - p`.
* `watcher_improves_survival` — a lower constant hazard gives higher survival at every horizon.
* `static_watcher_still_dies` — **but** if the watched accuracy stays below 1, the hazard is
  a positive constant, so survival still goes to 0 (`const_hazard_dies`).
* `learning_watcher_viable` — if the remaining error shrinks geometrically, `e·r^i` with
  `r < 1`, survival stays above `1 - e/(1 - r)` forever.

Reading: a Watcher with fixed accuracy buys time, not viability. Long-run viability needs the
error rate to fall over time, through a Brake that shrinks deviations (`BrakeViability`) or a
Watcher that improves. This is the second cross-organ link. It is a statement about the model
with independent, constant-accuracy decisions, which is an assumption (EMP?).
-/

namespace FiveOrgans.WatcherViability
open Finset FiveOrgans.ViabilityStochastic

theorem watcher_lowers_hazard {p α β r₁ r₀ q : ℝ}
    (hg : 0 < WatcherCompliance.accQ p α β r₁ r₀ q - p) :
    1 - WatcherCompliance.accQ p α β r₁ r₀ q < 1 - p := by linarith

/-- Lower constant hazard ⇒ higher survival at every horizon. -/
theorem watcher_improves_survival {h h' : ℝ} (hle : h' ≤ h) (h1 : h ≤ 1)
    (n : ℕ) : surv (fun _ => h) n ≤ surv (fun _ => h') n := by
  rw [surv_const, surv_const]
  exact pow_le_pow_left₀ (by linarith) (by linarith) n

/-- Strictly higher for every horizon `n ≥ 1` when the hazard is strictly lower. -/
theorem watcher_strictly_improves {h h' : ℝ} (hlt : h' < h) (h1 : h ≤ 1)
    {n : ℕ} (hn : n ≠ 0) : surv (fun _ => h) n < surv (fun _ => h') n := by
  rw [surv_const, surv_const]
  exact pow_lt_pow_left₀ (by linarith) (by linarith) hn

/-- **A Watcher with fixed accuracy below 1 still drives survival to 0.** -/
theorem static_watcher_still_dies {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {ε : ℝ} (hε : ε < 1) :
    ∃ n, surv (fun _ => 1 - a) n < 1 - ε :=
  const_hazard_dies (by linarith) (by linarith) hε

/-- **A Watcher whose remaining error shrinks geometrically is viable forever.** -/
theorem learning_watcher_viable {e r : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (n : ℕ) : 1 - e / (1 - r) ≤ surv (fun i => e * r ^ i) n := by
  apply budget_viable
  · intro i
    have h1 : r ^ i ≤ 1 := pow_le_one₀ hr0 hr1.le
    exact ⟨mul_nonneg he0 (pow_nonneg hr0 i), by nlinarith [pow_nonneg hr0 i]⟩
  · intro m
    calc ∑ i ∈ range m, e * r ^ i = e * ∑ i ∈ range m, r ^ i := by rw [mul_sum]
      _ ≤ e * (1 / (1 - r)) :=
          mul_le_mul_of_nonneg_left (BrakeViability.geom_le hr0 hr1 m) he0
      _ = e / (1 - r) := by ring

/-- Concrete: base accuracy 0.9 watched up to 0.99 still dies; error 0.01 halving each step
keeps survival ≥ 0.98 forever. -/
theorem instance_watcher :
    (∃ n, surv (fun _ => 1 - (99 : ℝ) / 100) n < 1 / 2) ∧
    ∀ n, (49 : ℝ) / 50 ≤ surv (fun i => 1 / 100 * (1 / 2 : ℝ) ^ i) n := by
  refine ⟨?_, fun n => ?_⟩
  · obtain ⟨n, hn⟩ := static_watcher_still_dies (a := 99 / 100) (ε := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
    exact ⟨n, by linarith⟩
  · have := learning_watcher_viable (e := 1 / 100) (r := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) n
    norm_num at this ⊢; linarith

end FiveOrgans.WatcherViability
