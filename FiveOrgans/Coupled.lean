import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# The coupled five-organ agent: one shared state, exact viability, all 32 ablations

Earlier modules treat each organ as its own hazard channel and multiply survivals. Here the five
functional capacities act on **one shared dynamical system**, so their effects interact.

## The model (deterministic, worst case)

Shared state: the essential variable `x` (deviation from the set point; organisational identity
holds while `|x| ≤ X`), the memory state `m`, and a resource stock `R`.

Environment `E`:
* shocks `d j ∈ [−D, D]` (any sequence; `D > 0`);
* drift `θ`: a constant `θ₀`, and, if `E.shift`, one regime shift to `θ₁` at an arbitrary
  time `s₀` (`|θ₀|, |θ₁| ≤ Θ`);
* actuation delay `E.delay` (zero or one step);
* `K` sensory channels; resource income per step; organ costs.

Residual entering the state at step `j`: `w j = θ j − m j + s(C)·d j`.

Each capacity is a mechanism inside this loop:
* **Skin** attenuates shocks by `σ`; **Spotlight** cancels the attended shock channel (factor
  `α`). So `s(C) = σ^[S] · α^[P]`.
* **Memory** holds a drift estimate `m` (calibrated to `θ₀`) that the controller cancels.
  Without Memory, `m = 0`.
* **Watcher** checks Memory against outcomes. After a shift it resets `m` to `θ₁` once it has
  detected the change, which takes `ℓ = 1` step with the Spotlight on it and `ℓ = K` steps
  without. A Watcher without Memory has nothing to reset.
* **Brake** caps the feedback gain: `k = 1/4` with Brake, `k = 1` (dead-beat) without.
  Loop with no delay: `x(n+1) = (1−k)·x n + w n`.
  Loop with delay: `x(n+2) = x(n+1) − k·x n + w(n+1)`.
* every organ draws its cost from the shared resource stock.

## Results

* `x_conv`: the state is the convolution of the residual with the loop's impulse response `h`.
* `stays_iff`: **exact viability.** Every admissible environment keeps `|x n| ≤ X` for every
  `n` ⇔ the loop is stable (Brake, or no delay) **and** `peak C E ≤ X`, where
  `peak = s(C)·D·L₁ + drift term`. Upper bound by convolution; matching lower bound by an
  explicit adversarial environment (constant push, a shift timed just before the check, or a
  resonant shock pattern when the loop is unstable).
* `resource_iff`: the stock stays nonnegative forever ⇔ cost ≤ income.
* `viable_iff`: both together, i.e. `Viable C E` is exactly the set of configurations that
  survive every admissible environment.
* Interaction theorems (general `E`): Brake necessary under delay and costly without it;
  Watcher redundant without Memory; Memory **harmful** without Watcher under shifts; Spotlight
  shortens the Watcher's latency; adding an organ can kill through cost.
* The 32-configuration tables live in `CoupledAblation`; micro-to-macro transfer in
  `CoupledTransfer`.

Scope. A deterministic worst case with one shift, linear loop, perfect detection after latency.
What a random environment does is an empirical question, tested in `analysis/coupled/`.
Nothing here is a claim about real systems.
-/

namespace FiveOrgans.Coupled
open Finset Filter Topology

/-! ### Configurations and environments -/

/-- A configuration: which of the five capacities are present. -/
structure Cfg where
  S : Bool
  M : Bool
  P : Bool
  B : Bool
  W : Bool
deriving DecidableEq

structure Env where
  D : ℝ
  Θ : ℝ
  X : ℝ
  σ : ℝ
  α : ℝ
  K : ℕ
  delay : Bool
  shift : Bool
  income : ℝ
  cS : ℝ
  cM : ℝ
  cP : ℝ
  cB : ℝ
  cW : ℝ

/-- Standing assumptions on an environment. -/
structure Env.Ok (E : Env) : Prop where
  D_pos : 0 < E.D
  Θ_nn : 0 ≤ E.Θ
  σ_pos : 0 < E.σ
  σ_le : E.σ ≤ 1
  α_pos : 0 < E.α
  α_le : E.α ≤ 1
  K_pos : 1 ≤ E.K

variable (C : Cfg) (E : Env)

/-- Shock factor after Skin and Spotlight. -/
noncomputable def sfac : ℝ := (if C.S then E.σ else 1) * (if C.P then E.α else 1)

/-- Watcher detection latency. -/
def lat : ℕ := if C.P then 1 else E.K

/-- Feedback gain. -/
noncomputable def gain : ℝ := if C.B then 1 / 4 else 1

def cost : ℝ := (if C.S then E.cS else 0) + (if C.M then E.cM else 0) +
  (if C.P then E.cP else 0) + (if C.B then E.cB else 0) + (if C.W then E.cW else 0)

/-! ### The two loops and their impulse responses -/

/-- No delay. -/
noncomputable def xa (k : ℝ) (w : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 - k) * xa k w n + w n

/-- One-step delay. -/
noncomputable def xd (k : ℝ) (w : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => w 0
  | n + 2 => xd k w (n + 1) - k * xd k w n + w (n + 1)

/-- Impulse response of the delayed loop. -/
noncomputable def hd (k : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | n + 2 => hd k (n + 1) - k * hd k n

theorem xa_conv (k : ℝ) (w : ℕ → ℝ) (n : ℕ) :
    xa k w n = ∑ t ∈ range n, (1 - k) ^ t * w (n - 1 - t) := by
  induction n with
  | zero => simp [xa]
  | succ n ih =>
    rw [xa, ih, sum_range_succ', mul_sum]
    simp only [pow_zero, one_mul, Nat.add_sub_cancel, Nat.sub_zero]
    congr 1
    refine sum_congr rfl fun t ht => ?_
    have : n - (t + 1) = n - 1 - t := by omega
    rw [this, pow_succ]; ring

theorem xd_conv (k : ℝ) (w : ℕ → ℝ) :
    ∀ n, xd k w n = ∑ t ∈ range n, hd k t * w (n - 1 - t)
  | 0 => by simp [xd]
  | 1 => by simp [xd, hd]
  | n + 2 => by
    rw [xd, xd_conv k w (n + 1), xd_conv k w n, sum_range_succ', sum_range_succ',
      sum_range_succ' _ n]
    have A : ∑ t ∈ range n, hd k (t + 1 + 1) * w (n + 2 - 1 - (t + 1 + 1)) =
        ∑ t ∈ range n, hd k (t + 1) * w (n - 1 - t) -
          k * ∑ t ∈ range n, hd k t * w (n - 1 - t) := by
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun t _ => ?_
      rw [show n + 2 - 1 - (t + 1 + 1) = n - 1 - t by omega, hd]; ring
    have B : ∑ t ∈ range n, hd k (t + 1) * w (n + 1 - 1 - (t + 1)) =
        ∑ t ∈ range n, hd k (t + 1) * w (n - 1 - t) :=
      sum_congr rfl fun t _ => by rw [show n + 1 - 1 - (t + 1) = n - 1 - t by omega]
    rw [A, B, show n + 2 - 1 - (0 + 1) = n by omega, show n + 2 - 1 - 0 = n + 1 by omega,
      show n + 1 - 1 - 0 = n by omega]
    simp only [hd]
    ring

/-- Impulse response of the configured loop. -/
noncomputable def h (t : ℕ) : ℝ := if E.delay then hd (gain C) t else (1 - gain C) ^ t

/-- The shared state driven by a residual sequence. -/
noncomputable def xC (w : ℕ → ℝ) : ℕ → ℝ := if E.delay then xd (gain C) w else xa (gain C) w

theorem xC_conv (w : ℕ → ℝ) (n : ℕ) : xC C E w n = ∑ t ∈ range n, h C E t * w (n - 1 - t) := by
  unfold xC h
  cases E.delay <;> simp [xa_conv, xd_conv]

/-! ### Impulse responses: closed forms, sign, monotonicity, total mass -/

/-- The loop is stable when the Brake is on or there is no delay. -/
def Stable : Prop := C.B = true ∨ E.delay = false

/-- Total mass `L₁ = ∑ h` of a stable loop. -/
noncomputable def L1 : ℝ := if C.B then 4 else 1

theorem hd_quarter : ∀ t : ℕ, hd (1 / 4) t = ((t : ℝ) + 1) / 2 ^ t
  | 0 => by simp [hd]
  | 1 => by norm_num [hd]
  | t + 2 => by
    rw [hd, hd_quarter (t + 1), hd_quarter t]
    push_cast
    field_simp
    ring

theorem hd_one_three (t : ℕ) : hd 1 (t + 3) = -hd 1 t := by
  rw [show t + 3 = (t + 1) + 2 from rfl, hd, show t + 1 + 1 = t + 2 from rfl, hd]
  ring

theorem hd_one_six (t : ℕ) : hd 1 (t + 6) = hd 1 t := by
  rw [show t + 6 = (t + 3) + 3 from rfl, hd_one_three, hd_one_three, neg_neg]

theorem hd_one_abs_block (m : ℕ) : ∑ i ∈ range 6, |hd 1 (6 * m + i)| = 4 := by
  have : ∀ i, hd 1 (6 * m + i) = hd 1 i := by
    intro i
    induction m with
    | zero => simp
    | succ m ih => rw [show 6 * (m + 1) + i = (6 * m + i) + 6 by ring, hd_one_six, ih]
  simp only [this]
  simp [sum_range_succ, hd]
  norm_num

theorem hd_one_abs_sum (m : ℕ) : ∑ t ∈ range (6 * m), |hd 1 t| = 4 * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 6 * (m + 1) = 6 * m + 6 by ring, sum_range_add, ih, hd_one_abs_block]
    push_cast; ring

variable {C E}

theorem h_B_delay (hB : C.B = true) (hd' : E.delay = true) (t : ℕ) :
    h C E t = ((t : ℝ) + 1) / 2 ^ t := by
  simp only [h, hd', gain, hB, ite_true]
  exact hd_quarter t

theorem h_B_nodelay (hB : C.B = true) (hd' : E.delay = false) (t : ℕ) :
    h C E t = (3 / 4 : ℝ) ^ t := by
  simp [h, hd', gain, hB]; norm_num

theorem h_nB_nodelay (hB : C.B = false) (hd' : E.delay = false) (t : ℕ) :
    h C E t = (0 : ℝ) ^ t := by
  simp [h, hd', gain, hB]

theorem h_nB_delay (hB : C.B = false) (hd' : E.delay = true) (t : ℕ) :
    h C E t = hd 1 t := by
  simp [h, hd', gain, hB]

theorem sum_quarter (n : ℕ) :
    ∑ t ∈ range n, ((t : ℝ) + 1) / 2 ^ t = 4 - 2 * ((n : ℝ) + 2) / 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, ih]; push_cast; field_simp; ring

theorem sum_threeq (n : ℕ) : ∑ t ∈ range n, (3 / 4 : ℝ) ^ t = 4 - 4 * (3 / 4 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring

theorem sum_zero_pow (n : ℕ) (hn : 1 ≤ n) : ∑ t ∈ range n, (0 : ℝ) ^ t = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ']; simp

theorem h_nonneg (hs : Stable C E) (t : ℕ) : 0 ≤ h C E t := by
  cases hB : C.B <;> cases hd' : E.delay
  · rw [h_nB_nodelay hB hd']; positivity
  · simp [Stable, hB, hd'] at hs
  · rw [h_B_nodelay hB hd']; positivity
  · rw [h_B_delay hB hd']; positivity

theorem h_anti (hs : Stable C E) : Antitone (h C E) := by
  refine antitone_nat_of_succ_le fun t => ?_
  cases hB : C.B <;> cases hd' : E.delay
  · rw [h_nB_nodelay hB hd', h_nB_nodelay hB hd']; simp
  · simp [Stable, hB, hd'] at hs
  · rw [h_B_nodelay hB hd', h_B_nodelay hB hd', pow_succ]
    have : 0 ≤ (3 / 4 : ℝ) ^ t := by positivity
    nlinarith
  · rw [h_B_delay hB hd', h_B_delay hB hd', div_le_div_iff₀ (by positivity) (by positivity),
      pow_succ]
    push_cast
    have : (0 : ℝ) ≤ 2 ^ t := by positivity
    have : (0 : ℝ) ≤ t := by positivity
    nlinarith

/-- Partial sums of a stable loop never exceed `L₁`. -/
theorem S_le (hs : Stable C E) (n : ℕ) : ∑ t ∈ range n, h C E t ≤ L1 C := by
  cases hB : C.B <;> cases hd' : E.delay
  · simp only [h_nB_nodelay hB hd', L1, hB]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [sum_zero_pow n hn]; simp
  · simp [Stable, hB, hd'] at hs
  · simp only [h_B_nodelay hB hd', L1, hB, sum_threeq, ite_true]
    have : 0 ≤ (3 / 4 : ℝ) ^ n := by positivity
    linarith
  · simp only [h_B_delay hB hd', L1, hB, sum_quarter, ite_true]
    have : 0 ≤ 2 * ((n : ℝ) + 2) / 2 ^ n := by positivity
    linarith

/-- Partial sums of a stable loop approach `L₁`. -/
theorem S_tendsto (hs : Stable C E) :
    Tendsto (fun n => ∑ t ∈ range n, h C E t) atTop (𝓝 (L1 C)) := by
  cases hB : C.B <;> cases hd' : E.delay
  · simp only [h_nB_nodelay hB hd', L1, hB]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [sum_zero_pow n hn]; simp
  · simp [Stable, hB, hd'] at hs
  · simp only [h_B_nodelay hB hd', L1, hB, sum_threeq, ite_true]
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)).const_mul 4
    simpa using (tendsto_const_nhds (x := (4 : ℝ))).sub this
  · simp only [h_B_delay hB hd', L1, hB, sum_quarter, ite_true]
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    have h3 : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 2) / 2 ^ n) atTop (𝓝 0) := by
      have := (h1.const_mul 2).add (h2.const_mul 4)
      simp only [mul_zero, add_zero] at this
      refine this.congr fun n => ?_
      rw [div_pow, one_pow]; field_simp; ring
    simpa using (tendsto_const_nhds (x := (4 : ℝ))).sub h3

/-- An antitone nonnegative sequence summed over any `ℓ` indices is at most its first `ℓ`
terms. -/
theorem sum_le_initial {g : ℕ → ℝ} (hg : Antitone g) :
    ∀ T : Finset ℕ, ∑ t ∈ T, g t ≤ ∑ t ∈ range T.card, g t := by
  intro T
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [sum_insert ha, card_insert_of_notMem ha, sum_range_succ]
    have hc : s.card ≤ a := by
      calc s.card ≤ (range a).card :=
            card_le_card fun x hx => mem_range.2 (hlt x hx)
        _ = a := card_range a
    linarith [hg hc]

theorem sum_le_initial' {g : ℕ → ℝ} (hg : Antitone g) (h0 : ∀ t, 0 ≤ g t) {T : Finset ℕ}
    {l : ℕ} (hT : T.card ≤ l) : ∑ t ∈ T, g t ≤ ∑ t ∈ range l, g t :=
  (sum_le_initial hg T).trans
    (sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hT) fun t _ _ => h0 t)

/-! ### Environment paths, residual, shared state -/

variable (C E)

/-- One realisation of the environment: initial drift, post-shift drift, shift time, shocks. -/
structure Path where
  θ0 : ℝ
  θ1 : ℝ
  s0 : ℕ
  d : ℕ → ℝ

/-- Admissible realisations. -/
def Adm (r : Path) : Prop := |r.θ0| ≤ E.Θ ∧ |r.θ1| ≤ E.Θ ∧ ∀ j, |r.d j| ≤ E.D

def theta (r : Path) (j : ℕ) : ℝ := if E.shift = true ∧ r.s0 ≤ j then r.θ1 else r.θ0

/-- Memory: calibrated to `θ₀`; reset to `θ₁` by the Watcher `lat` steps after a shift. -/
def mem (r : Path) (j : ℕ) : ℝ :=
  if C.M = true then
    (if E.shift = true ∧ C.W = true ∧ r.s0 + lat C E ≤ j then r.θ1 else r.θ0)
  else 0

/-- Residual entering the shared state. -/
noncomputable def wres (r : Path) (j : ℕ) : ℝ := theta E r j - mem C E r j + sfac C E * r.d j

/-- The essential variable along a realisation. -/
noncomputable def traj (r : Path) : ℕ → ℝ := xC C E (wres C E r)

noncomputable def Hs (l : ℕ) : ℝ := ∑ t ∈ range l, h C E t

/-- Worst-case drift contribution. -/
noncomputable def drift : ℝ :=
  if C.M = true then
    (if E.shift = true then
      (if C.W = true then 2 * E.Θ * Hs C E (lat C E) else 2 * E.Θ * L1 C) else 0)
  else E.Θ * L1 C

/-- Worst-case peak of `|x|`. -/
noncomputable def peak : ℝ := sfac C E * E.D * L1 C + drift C E

/-- Per-step bound on the drift residual. -/
noncomputable def rho (r : Path) (j : ℕ) : ℝ :=
  if C.M = true then
    (if E.shift = true then
      (if C.W = true then (if r.s0 ≤ j ∧ j < r.s0 + lat C E then 2 * E.Θ else 0) else 2 * E.Θ)
      else 0)
  else E.Θ

variable {C E}

theorem sfac_pos (hE : E.Ok) : 0 < sfac C E := by
  have := hE.σ_pos; have := hE.α_pos
  unfold sfac; split_ifs <;> positivity

theorem L1_pos : 0 < L1 C := by unfold L1; split_ifs <;> norm_num

theorem abs_sub_le2 {a b Θ : ℝ} (ha : |a| ≤ Θ) (hb : |b| ≤ Θ) : |a - b| ≤ 2 * Θ :=
  (abs_sub a b).trans (by linarith)

theorem dr_le {r : Path} (hr : Adm E r) (j : ℕ) :
    |theta E r j - mem C E r j| ≤ rho C E r j := by
  obtain ⟨h0, h1, -⟩ := hr
  have hΘ : 0 ≤ E.Θ := (abs_nonneg _).trans h0
  unfold theta mem rho
  by_cases hM : C.M = true <;> by_cases hS : E.shift = true <;> by_cases hW : C.W = true <;>
    simp only [hM, hS, hW, true_and, false_and, ite_true, ite_false, ite_true, ite_false,
      Bool.not_eq_true, Bool.false_eq_true, sub_zero, sub_self, abs_zero, le_refl] <;>
    (try split_ifs) <;>
    first
    | (exfalso; omega)
    | (simp only [sub_self, abs_zero]; positivity)
    | exact abs_sub_le2 h1 h0
    | exact abs_sub_le2 h0 h1
    | (simp only [sub_zero]; exact h0)
    | (simp only [sub_zero]; exact h1)
    | (simp [abs_sub_le2, *]; done)

theorem card_window (n a l : ℕ) :
    ((range n).filter fun t => a ≤ n - 1 - t ∧ n - 1 - t < a + l).card ≤ l := by
  calc _ ≤ (Ico a (a + l)).card := by
        refine card_le_card_of_injOn (fun t => n - 1 - t) (fun t ht => ?_) ?_
        · simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ht
          simp [ht.2.1, ht.2.2]
        · intro t₁ h₁ t₂ h₂ e
          simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at h₁ h₂
          simp only at e
          omega
    _ = l := by simp

theorem drift_sum_le (hs : Stable C E) (hE : E.Ok) (r : Path) (n : ℕ) :
    ∑ t ∈ range n, h C E t * rho C E r (n - 1 - t) ≤ drift C E := by
  have hΘ := hE.Θ_nn
  have hS := S_le hs n
  unfold rho drift
  by_cases hM : C.M = true <;> by_cases hS' : E.shift = true <;> by_cases hW : C.W = true <;>
    simp only [hM, hS', hW, ite_true, ite_false, ite_true, ite_false, Bool.false_eq_true,
      mul_zero, sum_const_zero, le_refl]
  all_goals first
    | (rw [← sum_mul]; nlinarith)
    | (rw [show ∑ t ∈ range n, h C E t * (2 * E.Θ) = 2 * E.Θ * ∑ t ∈ range n, h C E t by
          rw [mul_sum]; exact sum_congr rfl fun t _ => by ring]; nlinarith)
    | skip
  -- Memory + Watcher under a shift: only a window of `lat` steps is exposed
  have : ∑ t ∈ range n, h C E t *
      (if r.s0 ≤ n - 1 - t ∧ n - 1 - t < r.s0 + lat C E then 2 * E.Θ else 0) =
      2 * E.Θ * ∑ t ∈ (range n).filter
        (fun t => r.s0 ≤ n - 1 - t ∧ n - 1 - t < r.s0 + lat C E), h C E t := by
    rw [sum_filter, mul_sum]
    refine sum_congr rfl fun t _ => ?_
    split_ifs <;> ring
  rw [this]
  exact mul_le_mul_of_nonneg_left
    (sum_le_initial' (h_anti hs) (h_nonneg hs) (card_window _ _ _)) (by positivity)

/-- **Upper bound (sufficiency).** A stable configuration keeps `|x n| ≤ peak` along every
admissible realisation. -/
theorem traj_le (hs : Stable C E) (hE : E.Ok) {r : Path} (hr : Adm E r) (n : ℕ) :
    |traj C E r n| ≤ peak C E := by
  have hc := (sfac_pos (C := C) hE).le
  have hw : ∀ j, |wres C E r j| ≤ rho C E r j + sfac C E * E.D := by
    intro j
    have h1 := dr_le (C := C) hr j
    have h2 : |sfac C E * r.d j| ≤ sfac C E * E.D := by
      rw [abs_mul, abs_of_nonneg hc]; exact mul_le_mul_of_nonneg_left (hr.2.2 j) hc
    unfold wres
    exact (abs_add_le _ _).trans (by linarith)
  unfold traj
  rw [xC_conv]
  calc |∑ t ∈ range n, h C E t * wres C E r (n - 1 - t)|
      ≤ ∑ t ∈ range n, h C E t * (rho C E r (n - 1 - t) + sfac C E * E.D) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t _ => ?_)
        rw [abs_mul, abs_of_nonneg (h_nonneg hs t)]
        exact mul_le_mul_of_nonneg_left (hw _) (h_nonneg hs t)
    _ = ∑ t ∈ range n, h C E t * rho C E r (n - 1 - t) +
          sfac C E * E.D * ∑ t ∈ range n, h C E t := by
        rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun t _ => by ring
    _ ≤ drift C E + sfac C E * E.D * L1 C := by
        gcongr
        · exact drift_sum_le hs hE r n
        · have := hE.D_pos; positivity
        · exact S_le hs n
    _ = peak C E := by unfold peak; ring

/-- A constant residual gives `x n = v · ∑_{t<n} h t`. -/
theorem traj_const {r : Path} {v : ℝ} (hv : ∀ j, wres C E r j = v) (n : ℕ) :
    traj C E r n = v * ∑ t ∈ range n, h C E t := by
  unfold traj; rw [xC_conv, mul_sum]
  exact sum_congr rfl fun t _ => by rw [hv]; ring

/-- If `X < v·L₁` then a constant residual `v` eventually pushes `x` above `X`. -/
theorem exceed_const (hs : Stable C E) {r : Path} {v : ℝ} (hv : ∀ j, wres C E r j = v)
    (hp : E.X < v * L1 C) : ∃ n, E.X < traj C E r n := by
  have := ((S_tendsto hs).const_mul v).eventually (lt_mem_nhds hp)
  obtain ⟨n, hn⟩ := this.exists
  exact ⟨n, by rw [traj_const hv]; exact hn⟩

/-- **Lower bound (necessity), stable loop.** If `peak > X` some admissible realisation pushes
`x` above `X`. -/
theorem exceed (hs : Stable C E) (hE : E.Ok) (hp : E.X < peak C E) :
    ∃ r, Adm E r ∧ ∃ n, E.X < traj C E r n := by
  have hΘ := hE.Θ_nn
  have hD := hE.D_pos
  have aΘ : |E.Θ| ≤ E.Θ := (abs_of_nonneg hΘ).le
  have aΘ' : |-E.Θ| ≤ E.Θ := by rw [abs_neg]; exact aΘ
  have a0 : |(0 : ℝ)| ≤ E.Θ := by simpa using hΘ
  have aD : ∀ j : ℕ, |(fun _ : ℕ => E.D) j| ≤ E.D := fun _ => (abs_of_pos hD).le
  unfold peak drift at hp
  by_cases hM : C.M = true
  · by_cases hS : E.shift = true
    · by_cases hW : C.W = true
      · -- shift timed `lat` steps before the check
        simp only [hM, hS, hW, ite_true] at hp
        set l := lat C E
        have key : ∀ N, traj C E ⟨-E.Θ, E.Θ, N, fun _ => E.D⟩ (N + l) =
            sfac C E * E.D * ∑ t ∈ range (N + l), h C E t + 2 * E.Θ * Hs C E l := by
          intro N
          unfold traj; rw [xC_conv]
          have : ∀ t ∈ range (N + l), h C E t * wres C E ⟨-E.Θ, E.Θ, N, fun _ => E.D⟩
              (N + l - 1 - t) = sfac C E * E.D * h C E t +
                2 * E.Θ * (if t < l then h C E t else 0) := by
            intro t ht
            rw [mem_range] at ht
            unfold wres theta mem
            simp only [hS, hM, hW, true_and, ite_true]
            have e1 : ¬ (N + l ≤ N + l - 1 - t) := by omega
            rw [if_neg e1]
            by_cases ht' : t < l
            · rw [if_pos (by omega : N ≤ N + l - 1 - t), if_pos ht']; ring
            · rw [if_neg (by omega : ¬ N ≤ N + l - 1 - t), if_neg ht']; ring
          rw [sum_congr rfl this, sum_add_distrib, ← mul_sum, ← mul_sum, ← sum_filter]
          have : (range (N + l)).filter (· < l) = range l := by
            ext t; simp only [mem_filter, mem_range]; omega
          rw [this]; rfl
        have tend := ((S_tendsto hs).const_mul (sfac C E * E.D)).add_const (2 * E.Θ * Hs C E l)
        obtain ⟨N, hN⟩ := eventually_atTop.1 (tend.eventually (lt_mem_nhds hp))
        refine ⟨⟨-E.Θ, E.Θ, N, fun _ => E.D⟩, ⟨aΘ', aΘ, aD⟩, N + l, ?_⟩
        rw [key]; exact hN _ (by omega)
      · simp only [hM, hS, hW, ite_true, Bool.false_eq_true, ite_false] at hp
        refine ⟨⟨-E.Θ, E.Θ, 0, fun _ => E.D⟩, ⟨aΘ', aΘ, aD⟩,
          exceed_const hs (v := 2 * E.Θ + sfac C E * E.D) (fun j => ?_) (by linarith)⟩
        simp only [wres, theta, mem, hS, hM, hW, true_and, zero_le, ite_true,
          Bool.false_eq_true, false_and, and_false, ite_false]
        ring
    · simp only [hM, hS, ite_true, Bool.false_eq_true, ite_false, add_zero] at hp
      refine ⟨⟨0, 0, 0, fun _ => E.D⟩, ⟨a0, a0, aD⟩,
        exceed_const hs (v := sfac C E * E.D) (fun j => ?_) hp⟩
      simp only [wres, theta, mem]; split_ifs <;> ring
  · simp only [hM, Bool.false_eq_true, ite_false] at hp
    refine ⟨⟨E.Θ, E.Θ, 0, fun _ => E.D⟩, ⟨aΘ, aΘ, aD⟩,
      exceed_const hs (v := E.Θ + sfac C E * E.D) (fun j => ?_) (by linarith)⟩
    simp only [wres, theta, mem, hM, Bool.false_eq_true, ite_false]
    split_ifs <;> ring

/-- **Lower bound, unstable loop** (no Brake, delay): a resonant shock pattern drives `x`
past every bound. -/
theorem unstable_exceed (hB : C.B = false) (hd' : E.delay = true) (hE : E.Ok) (X : ℝ) :
    ∃ r, Adm E r ∧ ∃ n, X < traj C E r n := by
  have hc := sfac_pos (C := C) hE
  have hD := hE.D_pos
  obtain ⟨m, hm⟩ := exists_nat_gt (X / (4 * (sfac C E * E.D)))
  set n := 6 * m
  let d : ℕ → ℝ := fun j => E.D * (if 0 ≤ hd 1 (n - 1 - j) then 1 else -1)
  have a0 : |(0 : ℝ)| ≤ E.Θ := by simpa using hE.Θ_nn
  refine ⟨⟨0, 0, 0, d⟩, ⟨a0, a0, fun j => ?_⟩, n, ?_⟩
  · simp only [d]; split_ifs <;> simp [abs_of_pos hD]
  · unfold traj; rw [xC_conv]
    have : ∀ t ∈ range n, h C E t * wres C E ⟨0, 0, 0, d⟩ (n - 1 - t) =
        sfac C E * E.D * |hd 1 t| := by
      intro t ht
      rw [mem_range] at ht
      rw [h_nB_delay hB hd']
      simp only [wres, theta, mem, d, show n - 1 - (n - 1 - t) = t by omega]
      split_ifs <;> first
        | (rw [abs_of_nonneg (by assumption)]; ring)
        | (rw [abs_of_neg (by push_neg at *; assumption)]; ring)
        | ring
    rw [sum_congr rfl this, ← mul_sum, hd_one_abs_sum]
    rw [div_lt_iff₀ (by positivity)] at hm
    linarith

/-! ### Exact viability -/

/-- **Exact viability of the shared state.** Every admissible environment keeps `|x| ≤ X`
forever ⇔ the loop is stable and `peak ≤ X`. -/
theorem stays_iff (hE : E.Ok) :
    (∀ r, Adm E r → ∀ n, |traj C E r n| ≤ E.X) ↔ Stable C E ∧ peak C E ≤ E.X := by
  constructor
  · intro H
    by_cases hs : Stable C E
    · refine ⟨hs, not_lt.1 fun hp => ?_⟩
      obtain ⟨r, hr, n, hn⟩ := exceed hs hE hp
      exact absurd (H r hr n) (not_le.2 (hn.trans_le (le_abs_self _)))
    · exfalso
      have hB : C.B = false := by
        cases h : C.B
        · rfl
        · exact absurd (Or.inl h) hs
      have hd' : E.delay = true := by
        cases h : E.delay
        · exact absurd (Or.inr h) hs
        · rfl
      obtain ⟨r, hr, n, hn⟩ := unstable_exceed hB hd' hE E.X
      exact absurd (H r hr n) (not_le.2 (hn.trans_le (le_abs_self _)))
  · rintro ⟨hs, hp⟩ r hr n
    exact (traj_le hs hE hr n).trans hp

/-- **Resources.** The shared stock `R₀ + n·(income − cost)` stays nonnegative forever ⇔
cost ≤ income. -/
theorem resource_iff {R0 : ℝ} (h0 : 0 ≤ R0) :
    (∀ n : ℕ, 0 ≤ R0 + n * (E.income - cost C E)) ↔ cost C E ≤ E.income := by
  constructor
  · intro H
    by_contra hc
    push_neg at hc
    obtain ⟨n, hn⟩ := exists_nat_gt (R0 / (cost C E - E.income))
    rw [div_lt_iff₀ (by linarith)] at hn
    have := H n
    nlinarith
  · intro hc n
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith

variable (C E)

/-- The configuration survives every admissible environment with its resources. -/
def Viable : Prop := cost C E ≤ E.income ∧ Stable C E ∧ peak C E ≤ E.X

variable {C E}

/-- **Viability, exactly.** -/
theorem viable_iff (hE : E.Ok) {R0 : ℝ} (h0 : 0 ≤ R0) :
    Viable C E ↔ (∀ r, Adm E r → ∀ n : ℕ,
      |traj C E r n| ≤ E.X ∧ 0 ≤ R0 + n * (E.income - cost C E)) := by
  have a0 : Adm E ⟨0, 0, 0, fun _ => 0⟩ :=
    ⟨by simpa using hE.Θ_nn, by simpa using hE.Θ_nn, fun _ => by simpa using hE.D_pos.le⟩
  rw [Viable, ← resource_iff h0, ← stays_iff hE]
  constructor
  · rintro ⟨hR, hX⟩ r hr n; exact ⟨hX r hr n, hR n⟩
  · intro H
    exact ⟨fun n => (H _ a0 n).2, fun r hr n => (H r hr n).1⟩

/-! ### Closed form for the decision rule -/

variable (C E)

/-- Closed form of `Hs` for a stable loop and `ℓ ≥ 1`. -/
noncomputable def Hc (l : ℕ) : ℝ :=
  if C.B = true then (if E.delay = true then 4 - 2 * ((l : ℝ) + 2) / 2 ^ l
    else 4 - 4 * (3 / 4 : ℝ) ^ l) else 1

/-- Peak with `Hs` replaced by its closed form. -/
noncomputable def peakC : ℝ :=
  sfac C E * E.D * L1 C +
    (if C.M = true then
      (if E.shift = true then
        (if C.W = true then 2 * E.Θ * Hc C E (lat C E) else 2 * E.Θ * L1 C) else 0)
      else E.Θ * L1 C)

variable {C E}

theorem lat_pos (hE : E.Ok) : 1 ≤ lat C E := by
  unfold lat; split_ifs
  · rfl
  · exact hE.K_pos

theorem Hs_eq (hs : Stable C E) {l : ℕ} (hl : 1 ≤ l) : Hs C E l = Hc C E l := by
  unfold Hs Hc
  cases hB : C.B <;> cases hd' : E.delay
  · simp only [h_nB_nodelay hB hd', Bool.false_eq_true, ite_false]; exact sum_zero_pow l hl
  · simp [Stable, hB, hd'] at hs
  · simp only [h_B_nodelay hB hd', ite_true, Bool.false_eq_true, ite_false]; exact sum_threeq l
  · simp only [h_B_delay hB hd', ite_true]; exact sum_quarter l

theorem peak_eq (hE : E.Ok) (hs : Stable C E) : peak C E = peakC C E := by
  unfold peak peakC drift
  rw [Hs_eq hs (lat_pos hE)]

/-- **Decidable form of viability.** -/
theorem viable_closed (hE : E.Ok) :
    Viable C E ↔ cost C E ≤ E.income ∧ Stable C E ∧ peakC C E ≤ E.X := by
  unfold Viable
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨a, b, by rwa [← peak_eq hE b]⟩
  · rintro ⟨a, b, c⟩; exact ⟨a, b, by rwa [peak_eq hE b]⟩

/-! ### Interaction theorems (hold in every environment of the model) -/

/-- **Brake is mathematically necessary under delay.** -/
theorem brake_necessary (hd' : E.delay = true) (hB : C.B = false) : ¬ Viable C E := by
  rintro ⟨-, hs, -⟩
  rcases hs with h | h <;> simp_all

/-- **Watcher is redundant without Memory**: it changes nothing in the shared state. -/
theorem watcher_redundant (hM : C.M = false) :
    peak { C with W := true } E = peak { C with W := false } E := by
  simp [peak, drift, sfac, L1, hM]

/-- Adding a nonnegative-cost organ never relaxes the resource constraint. -/
theorem cost_W (hc : 0 ≤ E.cW) : cost { C with W := false } E ≤ cost { C with W := true } E := by
  simp only [cost]; split_ifs <;> simp <;> linarith

/-- Consequently a viable configuration stays viable when the redundant Watcher is removed. -/
theorem viable_drop_watcher (hM : C.M = false) (hc : 0 ≤ E.cW)
    (hv : Viable { C with W := true } E) : Viable { C with W := false } E := by
  obtain ⟨a, b, c⟩ := hv
  exact ⟨(cost_W hc).trans a, b, by rwa [← watcher_redundant hM]⟩

/-- **Memory without a Watcher is harmful under a shift**: stale memory doubles the
drift exposure. -/
theorem memory_harmful (hS : E.shift = true) (hW : C.W = false) (hΘ : 0 < E.Θ) :
    peak { C with M := false } E < peak { C with M := true } E := by
  have := L1_pos (C := C)
  simp only [peak, drift, sfac, L1, hS, hW, ite_true, Bool.false_eq_true, ite_false] at this ⊢
  nlinarith

/-- **Memory without drift is free**, and with constant drift it is strictly helpful. -/
theorem memory_helps_noshift (hS : E.shift = false) (hΘ : 0 < E.Θ) :
    peak { C with M := true } E < peak { C with M := false } E := by
  have := L1_pos (C := C)
  simp only [peak, drift, sfac, L1, hS, ite_true, Bool.false_eq_true, ite_false] at this ⊢
  nlinarith

theorem Hs_le_L1 (hs : Stable C E) (l : ℕ) : Hs C E l ≤ L1 C := S_le hs l

theorem Hs_mono (hs : Stable C E) {l l' : ℕ} (hl : l ≤ l') : Hs C E l ≤ Hs C E l' :=
  sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hl) fun t _ _ => h_nonneg hs t

/-- **Watcher helps whenever Memory is present** (stable loop). -/
theorem watcher_helps (hs : Stable C E) (hΘ : 0 ≤ E.Θ) :
    peak { C with W := true } E ≤ peak { C with W := false } E := by
  have h1 : Hs { C with W := true } E (lat { C with W := true } E) ≤ L1 C := by
    have : Stable { C with W := true } E := hs
    exact Hs_le_L1 this _
  simp only [peak, drift, sfac, L1] at h1 ⊢
  split_ifs at h1 ⊢ <;> first | contradiction | nlinarith

/-- **Spotlight never hurts the peak** (stable loop): it attenuates shocks and shortens the
Watcher's latency. -/
theorem spotlight_helps (hE : E.Ok) (hs : Stable C E) :
    peak { C with P := true } E ≤ peak { C with P := false } E := by
  have hT := hE.Θ_nn; have hD := hE.D_pos.le
  have hα := hE.α_pos; have hα1 := hE.α_le; have hσ := hE.σ_pos; have hσ1 := hE.σ_le
  have hm : Hs { C with P := true } E 1 ≤ Hs { C with P := false } E E.K := by
    have : Stable { C with P := false } E := hs
    exact Hs_mono this hE.K_pos
  have hL := L1_pos (C := C)
  have hsf : (if C.S = true then E.σ else 1) * E.α * E.D * L1 C ≤
      (if C.S = true then E.σ else 1) * 1 * E.D * L1 C := by
    have : 0 ≤ (if C.S = true then E.σ else 1) := by split_ifs <;> positivity
    gcongr
  simp only [peak, drift, sfac, lat, L1, ite_true, Bool.false_eq_true, ite_false] at hm hsf hL ⊢
  split_ifs at hm hsf hL ⊢ <;> first | contradiction | nlinarith

/-- **Skin never hurts the peak.** -/
theorem skin_helps (hE : E.Ok) :
    peak { C with S := true } E ≤ peak { C with S := false } E := by
  have hD := hE.D_pos.le; have hσ1 := hE.σ_le
  have hL := L1_pos (C := C)
  have : 0 ≤ (if C.P = true then E.α else 1) := by
    have := hE.α_pos; split_ifs <;> positivity
  simp only [peak, drift, sfac, lat, L1, ite_true, Bool.false_eq_true, ite_false] at hL ⊢
  have : E.σ * (if C.P = true then E.α else 1) * E.D * (if C.B = true then 4 else 1) ≤
      1 * (if C.P = true then E.α else 1) * E.D * (if C.B = true then 4 else 1) := by
    have : (0 : ℝ) ≤ (if C.B = true then 4 else 1) := by split_ifs <;> norm_num
    gcongr
  have e : ∀ l, Hs { S := true, M := C.M, P := C.P, B := C.B, W := C.W } E l =
      Hs { S := false, M := C.M, P := C.P, B := C.B, W := C.W } E l := fun _ => rfl
  rw [e]
  linarith

/-- **A brake without delay is harmful**: it slows a dead-beat loop and amplifies the peak
(stable either way). -/
theorem brake_harmful_nodelay (hE : E.Ok) (hd' : E.delay = false) :
    peak { C with B := false } E < peak { C with B := true } E := by
  have hD := hE.D_pos; have hT := hE.Θ_nn
  have hsf := sfac_pos (C := C) (E := E) hE
  have hl := lat_pos (C := C) (E := E) hE
  have e1 : Hs { C with B := true } E (lat C E) = 4 - 4 * (3 / 4 : ℝ) ^ (lat C E) := by
    rw [Hs_eq (Or.inr hd') hl]; simp [Hc, hd']
  have e0 : Hs { C with B := false } E (lat C E) = 1 := by
    rw [Hs_eq (Or.inr hd') hl]; simp [Hc]
  have hp : (3 / 4 : ℝ) ^ lat C E ≤ 3 / 4 := by
    calc (3 / 4 : ℝ) ^ lat C E ≤ (3 / 4) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hl
      _ = 3 / 4 := pow_one _
  have hsf' : sfac { C with B := false } E = sfac C E := rfl
  have hsf'' : sfac { C with B := true } E = sfac C E := rfl
  have hlat : lat { C with B := true } E = lat C E := rfl
  have hlat' : lat { C with B := false } E = lat C E := rfl
  simp only [peak, drift, L1, hsf', hsf'', hlat, hlat', e1, e0, ite_true, Bool.false_eq_true,
    ite_false]
  split_ifs <;> first | contradiction | nlinarith

end FiveOrgans.Coupled
