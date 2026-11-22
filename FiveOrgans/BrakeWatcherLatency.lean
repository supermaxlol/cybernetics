import FiveOrgans.BrakeDelayExact

/-!
# Brake × Watcher: review latency shrinks the brake's stable window

A Watcher that reviews each correction before it is applied adds latency to the brake loop.
Model: the brake acts on information `d` steps old; review adds `w` more steps, so the loop runs
with delay `d + w`: `x (n+d+w+1) = x (n+d+w) − k x n`. By `BrakeDelayExact.exact_window` the
stable gains are `0 < k < kEdge (d+w)` (bounded) and `k > kEdge (d+w)` gives an unbounded
trajectory.

* `kEdge_strictAnti` — the edge `kEdge d = 2 sin(π/(2(2d+1)))` strictly falls with delay.
* `kEdge_le` — `kEdge d ≤ π/(2d+1)`, so the edge goes to `0`.
* `latency_destabilizes` — for any `w ≥ 1` there are gains that are stable without review and
  unstable with it (every gain strictly between the two edges).
* `latency_breaks_any_gain` — **every fixed positive gain is destabilized by enough review
  latency.**
* `safe_gain_under_latency` — a gain that keeps every trajectory bounded under latency `W` must
  satisfy `k ≤ kEdge (d+W)`; so adding a Watcher forces a weaker brake.

Reading. `WatcherViability` shows a Watcher lowers the per-decision hazard. This module shows
the price when the Watcher sits *inside* the brake loop: it narrows (and eventually closes) the
brake's stable gain window. The two organs trade off; they are not independent once the Watcher
gates the Brake. Scope: the linear delayed brake only; that review acts as pure added delay is an
assumption (EMP?). A Watcher that runs in parallel (no gating) adds no delay and is not covered.
-/

namespace FiveOrgans.BrakeWatcherLatency
open Real FiveOrgans.BrakeDelayEdge FiveOrgans.BrakeDelayExact

theorem θ_pos' (d : ℕ) : 0 < θ d := by unfold θ; positivity

theorem θ_le_pi (d : ℕ) : θ d ≤ π := by
  unfold θ
  rw [div_le_iff₀ (by positivity)]
  nlinarith [pi_pos, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

theorem θ_strictAnti {d d' : ℕ} (h : d < d') : θ d' < θ d := by
  unfold θ
  have : (d : ℝ) < d' := by exact_mod_cast h
  apply div_lt_div_of_pos_left pi_pos (by positivity)
  linarith

/-- **The stable edge strictly falls with delay.** -/
theorem kEdge_strictAnti {d d' : ℕ} (h : d < d') : kEdge d' < kEdge d := by
  unfold kEdge
  have h1 := θ_strictAnti h
  have h2 := θ_pos' d'
  have h3 := θ_le_pi d
  have : sin (θ d' / 2) < sin (θ d / 2) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [pi_pos]) (by linarith) (by linarith)
  linarith

/-- The edge is at most `π/(2d+1)`, hence tends to `0`. -/
theorem kEdge_le (d : ℕ) : kEdge d ≤ π / (2 * d + 1) := by
  unfold kEdge
  have := Real.sin_le (by linarith [θ_pos' d] : 0 ≤ θ d / 2)
  have : θ d = π / (2 * d + 1) := rfl
  linarith

/-- **Review latency destabilizes some gains:** strictly between the two edges, the brake is
bounded without review and has an unbounded trajectory with review latency `w ≥ 1`. -/
theorem latency_destabilizes {d w : ℕ} (hd : 1 ≤ d) (hw : 1 ≤ w) {k : ℝ}
    (hlo : kEdge (d + w) < k) (hhi : k < kEdge d) :
    (∀ x : ℕ → ℝ, (∀ n, x (n + d + 1) = x (n + d) - k * x n) → ∃ B, ∀ n, |x n| ≤ B) ∧
    (∃ x : ℕ → ℝ, (∀ n, x (n + (d + w) + 1) = x (n + (d + w)) - k * x n) ∧
        ∀ B, ∃ n, B < |x n|) := by
  have hk0 : 0 < k := (edge_pos (d + w)).trans hlo
  exact ⟨fun x hrec => exact_edge_stable hd hk0 hhi hrec,
    exact_edge_unstable (by omega) hlo⟩

/-- Such gains exist for every `w ≥ 1`. -/
theorem latency_gap {d w : ℕ} (hw : 1 ≤ w) : kEdge (d + w) < kEdge d :=
  kEdge_strictAnti (by omega)

/-- **Every fixed positive gain is destabilized by enough review latency.** -/
theorem latency_breaks_any_gain (d : ℕ) {k : ℝ} (hk : 0 < k) :
    ∃ W : ℕ, ∃ x : ℕ → ℝ, (∀ n, x (n + (d + W) + 1) = x (n + (d + W)) - k * x n) ∧
        ∀ B, ∃ n, B < |x n| := by
  obtain ⟨N, hN⟩ := exists_nat_gt (π / k)
  refine ⟨N + 1, exact_edge_unstable (by omega) ?_⟩
  have hle := kEdge_le (d + (N + 1))
  have hpos : (0 : ℝ) < 2 * ((d + (N + 1) : ℕ) : ℝ) + 1 := by positivity
  have hbig : π / k < 2 * ((d + (N + 1) : ℕ) : ℝ) + 1 := by
    push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have : π / (2 * ((d + (N + 1) : ℕ) : ℝ) + 1) < k := by
    rw [div_lt_iff₀ hpos]
    rw [div_lt_iff₀ hk] at hbig
    linarith
  linarith

/-- **A Watcher in the loop forces a weaker brake:** if gain `k` keeps every trajectory bounded
under total delay `d + W ≥ 1`, then `k ≤ kEdge (d + W)`. -/
theorem safe_gain_under_latency {d W : ℕ} (hdW : 1 ≤ d + W) {k : ℝ}
    (hstable : ∀ x : ℕ → ℝ, (∀ n, x (n + (d + W) + 1) = x (n + (d + W)) - k * x n) →
        ∃ B, ∀ n, |x n| ≤ B) : k ≤ kEdge (d + W) := by
  by_contra h
  push Not at h
  obtain ⟨x, hrec, hun⟩ := exact_edge_unstable hdW h
  obtain ⟨B, hB⟩ := hstable x hrec
  obtain ⟨n, hn⟩ := hun B
  linarith [hB n]

end FiveOrgans.BrakeWatcherLatency
