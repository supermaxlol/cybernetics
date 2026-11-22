import FiveOrgans.Skin

/-!
# Selective skin: a filter that tells nutrient from threat widens the window

`Skin.lean` has one permeability `ρ` for everything, so feeding and protecting conflict, and a
skin that does both exists iff `ρmin · D ≤ (1 - μ) K` (`skin_window`). Here the outside has two
channels:

* a **nutrient** channel `dn` with `|dn| ≤ Dn` (the organism must let it in at rate `ρn ≥ ρmin`),
* a **threat** channel `dt` with `|dt| ≤ Dt`, let in at rate `ρt`.

Both perturb the interior: `s (k+1) = μ s k + ρn dn k + ρt dt k`.

A filter with **leakage** `λ ∈ [0,1]` cannot pass nutrients without also passing threats at
rate `ρt = λ · ρn`. `λ = 1` is the old undiscriminating skin. `λ = 0` is a perfect filter.

* `sel_invariant` / `sel_breach` — the invariance threshold is `μK + ρn Dn + ρt Dt ≤ K`.
* `leaky_window` — **a skin that feeds and protects exists iff `ρmin (Dn + λ Dt) ≤ (1-μ) K`.**
* `window_mono` — less leakage never shrinks the window.
* `selective_beats_uniform` — there are worlds in which **no** undiscriminating skin can both
  feed and protect, but a perfect filter can.

This mirrors `TwoSpeed` and `WatcherDiscerning`: one parameter for two conflicting jobs fails,
while discriminating between them restores the window. Scope: two scalar channels, known
bounds, a fixed leakage. How the filter tells the channels apart is not modelled (EMP?).
-/

namespace FiveOrgans.SkinSelective

/-- Two-channel interior dynamics. -/
def traj2 (μ ρn ρt s₀ : ℝ) (dn dt : ℕ → ℝ) : ℕ → ℝ
  | 0 => s₀
  | k + 1 => μ * traj2 μ ρn ρt s₀ dn dt k + ρn * dn k + ρt * dt k

/-- The two-channel skin is the one-channel skin driven by the combined inflow. -/
theorem traj2_eq (μ ρn ρt s₀ : ℝ) (dn dt : ℕ → ℝ) (k : ℕ) :
    traj2 μ ρn ρt s₀ dn dt k = Skin.traj μ 1 s₀ (fun j => ρn * dn j + ρt * dt j) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [traj2, Skin.traj, ih]; ring

/-- **Invariance:** below the threshold every admissible pair of inflows keeps it viable. -/
theorem sel_invariant {μ ρn ρt K Dn Dt s₀ : ℝ} {dn dt : ℕ → ℝ} (hμ : 0 ≤ μ) (hn : 0 ≤ ρn)
    (ht : 0 ≤ ρt) (h : μ * K + ρn * Dn + ρt * Dt ≤ K) (hdn : ∀ k, |dn k| ≤ Dn)
    (hdt : ∀ k, |dt k| ≤ Dt) (hs : |s₀| ≤ K) (k : ℕ) :
    |traj2 μ ρn ρt s₀ dn dt k| ≤ K := by
  rw [traj2_eq]
  refine Skin.skin_invariant (D := ρn * Dn + ρt * Dt) hμ zero_le_one (by linarith) ?_ hs k
  intro j
  calc |ρn * dn j + ρt * dt j| ≤ |ρn * dn j| + |ρt * dt j| := abs_add_le _ _
    _ = ρn * |dn j| + ρt * |dt j| := by rw [abs_mul, abs_mul, abs_of_nonneg hn, abs_of_nonneg ht]
    _ ≤ ρn * Dn + ρt * Dt := add_le_add (mul_le_mul_of_nonneg_left (hdn j) hn)
        (mul_le_mul_of_nonneg_left (hdt j) ht)

/-- **Breach:** above the threshold the steady maximal push from the edge leaves in one step. -/
theorem sel_breach {μ ρn ρt K Dn Dt : ℝ} (h : K < μ * K + ρn * Dn + ρt * Dt) :
    K < traj2 μ ρn ρt K (fun _ => Dn) (fun _ => Dt) 1 := by
  simp only [traj2]; linarith

/-- **The leaky window:** feeding (`ρn ≥ ρmin`) and protecting are jointly possible iff
`ρmin (Dn + lk Dt) ≤ (1 - μ) K`. -/
theorem leaky_window {μ K Dn Dt ρmin lk : ℝ} (hDn : 0 ≤ Dn) (hDt : 0 ≤ Dt)
    (hlk : 0 ≤ lk) :
    (∃ ρn, ρmin ≤ ρn ∧ μ * K + ρn * Dn + (lk * ρn) * Dt ≤ K) ↔
      ρmin * (Dn + lk * Dt) ≤ (1 - μ) * K := by
  constructor
  · rintro ⟨ρn, hge, hle⟩
    have hW : 0 ≤ Dn + lk * Dt := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hge hW]
  · intro h
    exact ⟨ρmin, le_rfl, by nlinarith⟩

/-- **Less leakage never shrinks the window.** -/
theorem window_mono {μ K Dn Dt ρmin lk lk' : ℝ} (hρ : 0 ≤ ρmin) (hDt : 0 ≤ Dt) (hlk : lk' ≤ lk)
    (h : ρmin * (Dn + lk * Dt) ≤ (1 - μ) * K) : ρmin * (Dn + lk' * Dt) ≤ (1 - μ) * K := by
  have : ρmin * (lk' * Dt) ≤ ρmin * (lk * Dt) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlk hDt) hρ
  nlinarith

/-- **Selective beats uniform:** when `ρmin Dn ≤ (1-μ)K < ρmin (Dn + Dt)`, no undiscriminating skin
(`lk = 1`) both feeds and protects, but a perfect filter (`lk = 0`) does. -/
theorem selective_beats_uniform {μ K Dn Dt ρmin : ℝ} (hDn : 0 ≤ Dn)
    (hDt : 0 ≤ Dt) (hsel : ρmin * Dn ≤ (1 - μ) * K) (hunif : (1 - μ) * K < ρmin * (Dn + Dt)) :
    (¬ ∃ ρn, ρmin ≤ ρn ∧ μ * K + ρn * Dn + (1 * ρn) * Dt ≤ K) ∧
    (∃ ρn, ρmin ≤ ρn ∧ μ * K + ρn * Dn + (0 * ρn) * Dt ≤ K) := by
  refine ⟨fun hex => ?_, (leaky_window hDn hDt le_rfl).mpr (by simpa using hsel)⟩
  have := (leaky_window hDn hDt zero_le_one).mp hex
  linarith [show ρmin * (Dn + 1 * Dt) = ρmin * (Dn + Dt) by ring]

/-- Non-vacuity: `μ = 1/2, K = 1, Dn = 1, Dt = 1, ρmin = 1/2`. Uniform needs `1 ≤ 1/2` (fails);
a perfect filter needs `1/2 ≤ 1/2` (holds). -/
theorem selective_instance :
    (¬ ∃ ρn : ℝ, 1 / 2 ≤ ρn ∧ 1 / 2 * 1 + ρn * 1 + (1 * ρn) * 1 ≤ 1) ∧
    (∃ ρn : ℝ, 1 / 2 ≤ ρn ∧ 1 / 2 * 1 + ρn * 1 + (0 * ρn) * 1 ≤ 1) :=
  selective_beats_uniform (μ := 1 / 2) (K := 1) (Dn := 1) (Dt := 1) (ρmin := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end FiveOrgans.SkinSelective
