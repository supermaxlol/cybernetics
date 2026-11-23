import FiveOrgans.Coupled

/-!
# Cross-scale transfer for the coupled model

**Micro level.** `N` sub-units share one configuration and one environment realisation. Unit `i`
also receives its own idiosyncratic input error `ε i j` with `|ε i j| ≤ η`. The **macro
variable** is the average state.

- `xC_linear`: the loop is linear, so the average of the unit states is the loop applied to the
  average input.
- `macro_micro_gap`: the aggregate is within `η·L₁` of the single macro loop at every time.
- `transfer_viable`: if `peak + η·L₁ ≤ X`, then every micro realisation keeps the aggregate
  inside `X`.
- `transfer_failure`: if `X + η·L₁ < peak` (stable loop), then for **every** choice of
  micro-errors some admissible realisation pushes the aggregate past `X`.
- `transfer_intervention`: both statements hold for every configuration. Macro predictions
  of an intervention (switching capacities on or off for all units) therefore transfer to the
  micro level whenever the margin condition holds.

Validity conditions (explicit; none is checked against real data):
- shared configuration across units;
- linear dynamics;
- bounded idiosyncratic error.

*Partial* interventions, where only some units lose a capacity, make the units heterogeneous.
That case is not covered here and is tested in simulation (`analysis/coupled/`).
-/

namespace FiveOrgans.CoupledTransfer
open FiveOrgans.Coupled Finset Filter Topology

variable {C : Cfg} {E : Env}

/-- Linearity of the shared loop in its input. -/
theorem xC_linear {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → ℕ → ℝ) (n : ℕ) :
    xC C E (fun j => ∑ i ∈ s, c i * u i j) n = ∑ i ∈ s, c i * xC C E (u i) n := by
  rw [xC_conv]
  simp_rw [xC_conv, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun t _ => sum_congr rfl fun i _ => by ring

theorem xC_add (w e : ℕ → ℝ) (n : ℕ) :
    xC C E (fun j => w j + e j) n = xC C E w n + xC C E e n := by
  simp only [xC_conv, ← sum_add_distrib]
  exact sum_congr rfl fun t _ => by ring

theorem xC_err_le (hs : Stable C E) {e : ℕ → ℝ} {η : ℝ} (he : ∀ j, |e j| ≤ η) (n : ℕ) :
    |xC C E e n| ≤ η * L1 C := by
  rw [xC_conv]
  have hη : 0 ≤ η := (abs_nonneg _).trans (he 0)
  calc |∑ t ∈ range n, h C E t * e (n - 1 - t)|
      ≤ ∑ t ∈ range n, h C E t * η := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t _ => ?_)
        rw [abs_mul, abs_of_nonneg (h_nonneg hs t)]
        exact mul_le_mul_of_nonneg_left (he _) (h_nonneg hs t)
    _ = η * ∑ t ∈ range n, h C E t := by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    _ ≤ η * L1 C := mul_le_mul_of_nonneg_left (S_le hs n) hη

/-- Average state of `N` units, unit `i` driven by `wres + ε i`. -/
noncomputable def agg (N : ℕ) (r : Path) (ε : Fin N → ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 / N : ℝ) * ∑ i, xC C E (fun j => wres C E r j + ε i j) n

/-- **Macro–micro gap.** The aggregate stays within `η·L₁` of the macro loop. -/
theorem macro_micro_gap (hs : Stable C E) {N : ℕ} (hN : 0 < N) (r : Path)
    {ε : Fin N → ℕ → ℝ} {η : ℝ} (hε : ∀ i j, |ε i j| ≤ η) (n : ℕ) :
    |agg (C := C) (E := E) N r ε n - traj C E r n| ≤ η * L1 C := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set e : ℕ → ℝ := fun j => (1 / N : ℝ) * ∑ i, ε i j
  have he : ∀ j, |e j| ≤ η := by
    intro j
    simp only [e]
    rw [abs_mul, abs_of_pos (by positivity), one_div, inv_mul_le_iff₀ hN']
    calc |∑ i, ε i j| ≤ ∑ i : Fin N, |ε i j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, η := sum_le_sum fun i _ => hε i j
      _ = N * η := by simp
  have key : agg (C := C) (E := E) N r ε n = traj C E r n + xC C E e n := by
    unfold agg traj
    simp_rw [xC_add]
    rw [sum_add_distrib, mul_add]
    have h1 : (1 / N : ℝ) * ∑ _i : Fin N, xC C E (wres C E r) n = xC C E (wres C E r) n := by
      simp; field_simp
    have h2 : (1 / N : ℝ) * ∑ i : Fin N, xC C E (ε i) n = xC C E e n := by
      simp only [e]
      have := xC_linear (C := C) (E := E) (univ : Finset (Fin N)) (fun _ => (1 / N : ℝ)) ε n
      rw [← mul_sum] at this
      simp only [← mul_sum] at this
      exact this.symm
    rw [h1, h2]
  rw [key, add_sub_cancel_left]
  exact xC_err_le hs he n

/-- **Viability transfers up with margin.** -/
theorem transfer_viable (hs : Stable C E) (hE : E.Ok) {N : ℕ} (hN : 0 < N) {η : ℝ}
    (hm : peak C E + η * L1 C ≤ E.X) {r : Path} (hr : Adm E r)
    {ε : Fin N → ℕ → ℝ} (hε : ∀ i j, |ε i j| ≤ η) (n : ℕ) :
    |agg (C := C) (E := E) N r ε n| ≤ E.X := by
  have g := macro_micro_gap hs hN r hε n
  have t := traj_le hs hE hr n
  calc |agg (C := C) (E := E) N r ε n|
      = |(agg (C := C) (E := E) N r ε n - traj C E r n) + traj C E r n| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ η * L1 C + peak C E := add_le_add g t
    _ ≤ E.X := by linarith

/-- **Failure transfers up with margin.** If `X + η·L₁ < peak`, then for every choice of
bounded micro-errors some admissible realisation drives the aggregate above `X`. -/
theorem transfer_failure (hs : Stable C E) (hE : E.Ok) {N : ℕ} (hN : 0 < N) {η : ℝ}
    (hm : E.X + η * L1 C < peak C E) (ε : Fin N → ℕ → ℝ) (hε : ∀ i j, |ε i j| ≤ η) :
    ∃ r, Adm E r ∧ ∃ n, E.X < agg (C := C) (E := E) N r ε n := by
  let E' : Env := { E with X := E.X + η * L1 C }
  have hE' : E'.Ok := ⟨hE.D_pos, hE.Θ_nn, hE.σ_pos, hE.σ_le, hE.α_pos, hE.α_le, hE.K_pos⟩
  have hs' : Stable C E' := hs
  have hp : E'.X < peak C E' := hm
  obtain ⟨r, hr, n, hn⟩ := exceed hs' hE' hp
  refine ⟨r, hr, n, ?_⟩
  have g := macro_micro_gap hs hN r hε n
  have e1 : traj C E' r n = traj C E r n := rfl
  rw [e1] at hn
  have := (abs_le.1 g).1
  simp only [E'] at hn
  linarith

/-- **Interventions transfer.** For any configuration (any intervention applied to all units),
outside the band `|peak − X| ≤ η·L₁` the micro verdict equals the macro verdict. -/
theorem transfer_intervention (hE : E.Ok) {N : ℕ} (hN : 0 < N) {η : ℝ} (C' : Cfg)
    (hs : Stable C' E) (hband : η * L1 C' < |peak C' E - E.X|) :
    (Viable C' E → ∀ r, Adm E r → ∀ ε : Fin N → ℕ → ℝ, (∀ i j, |ε i j| ≤ η) →
        ∀ n, |agg (C := C') (E := E) N r ε n| ≤ E.X) ∧
      (¬ Viable C' E → cost C' E ≤ E.income → ∀ ε : Fin N → ℕ → ℝ, (∀ i j, |ε i j| ≤ η) →
        ∃ r, Adm E r ∧ ∃ n, E.X < agg (C := C') (E := E) N r ε n) := by
  constructor
  · rintro ⟨-, -, hp⟩ r hr ε hε n
    have : peak C' E + η * L1 C' ≤ E.X := by
      rcases le_or_gt (peak C' E) E.X with h | h
      · rw [abs_of_nonpos (by linarith)] at hband; linarith
      · linarith
    exact transfer_viable hs hE hN this hr hε n
  · intro hv hc ε hε
    have hp : E.X < peak C' E := by
      by_contra h; exact hv ⟨hc, hs, not_lt.1 h⟩
    rw [abs_of_pos (by linarith)] at hband
    exact transfer_failure hs hE hN (by linarith) ε hε

end FiveOrgans.CoupledTransfer
