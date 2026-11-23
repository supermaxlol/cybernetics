import FiveOrgans.CoupledTransfer

/-!
# Partial interventions, adaptation and resistance to destabilising feedback

**1. Heterogeneous units (partial interventions).** Unit `i` runs configuration `Cs i`. All units
share one environment realisation, and each has its own bounded error `ε i`. The macro variable
is the average state `aggH`.
- `partial_bound`: if every unit is stable, `|aggH| ≤ (1/N) Σᵢ (peakᵢ + η·L₁ᵢ)`. This is a
  mean-field bound and needs no shared configuration.
- `partial_viable`: if every unit is viable with margin `η·L₁ᵢ`, the aggregate is viable. Any
  mixture of viable configurations transfers.
- `partial_unstable`: under delay, if **even one** of the `N` units lacks the Brake, some admissible
  shared realisation (with `ε = 0`) drives the aggregate past every bound. In the worst case a
  macro verdict based on the majority configuration fails for **every** ablated fraction
  `f ≥ 1/N`.
- The pre-registered simulation (H9) found the opposite in the average case: degradation is
  gradual. Worst-case and average-case cross-scale claims therefore differ.

**2. Adaptation.** After a drift shift at `s0`, define the memory error `θ − m`.
- `adapt_exact`: with Memory and Watcher, for `j ≥ s0` the error is zero ⇔ `j ≥ s0 + lat` or the
  shift was null. The adaptation time is exactly the Watcher latency (1 with Spotlight, else `K`).
- `no_adapt_without_watcher`: with Memory and no Watcher, the error stays `θ₁ − θ₀` forever.
- `no_baseline_without_memory`: without Memory the error is `θ` itself at every step.

**3. Resistance to destabilising feedback.** A parasitic positive feedback `δ ≥ 0` is added to
the undelayed loop: `x' = (1 − k)x + δx + w`. Its impulse response is `(1 − (k − δ))^t`.
- `resist_iff`: for `0 < k ≤ 1`, the loop keeps a finite gain bound ⇔ `δ < k`.
- `brake_resistance_nodelay`: the Brake (`k = 1/4`) tolerates only `δ < 1/4`; without it
  (`k = 1`) the loop tolerates `δ < 1`. The Brake, which is necessary under delay, cuts the
  feedback margin by a factor of 4 when there is no delay.
- The delayed case (Jury criterion) is **not** formalised here. It is measured in
  `analysis/coupled/`.
-/

namespace FiveOrgans.CoupledPartial
open FiveOrgans.Coupled FiveOrgans.CoupledTransfer Finset Filter Topology

variable {E : Env}

/-! ### 1. Heterogeneous units -/

/-- Average state of `N` heterogeneous units. -/
noncomputable def aggH {N : ℕ} (Cs : Fin N → Cfg) (r : Path) (ε : Fin N → ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 / N : ℝ) * ∑ i, xC (Cs i) E (fun j => wres (Cs i) E r j + ε i j) n

theorem unit_le {C : Cfg} (hs : Stable C E) (hE : E.Ok) {r : Path} (hr : Adm E r)
    {e : ℕ → ℝ} {η : ℝ} (he : ∀ j, |e j| ≤ η) (n : ℕ) :
    |xC C E (fun j => wres C E r j + e j) n| ≤ peak C E + η * L1 C := by
  rw [xC_add]
  exact (abs_add_le _ _).trans (add_le_add (traj_le hs hE hr n) (xC_err_le hs he n))

/-- **Mean-field bound** for heterogeneous stable units. -/
theorem partial_bound (hE : E.Ok) {N : ℕ} (hN : 0 < N) (Cs : Fin N → Cfg)
    (hs : ∀ i, Stable (Cs i) E) {r : Path} (hr : Adm E r) {ε : Fin N → ℕ → ℝ} {η : ℝ}
    (hε : ∀ i j, |ε i j| ≤ η) (n : ℕ) :
    |aggH (E := E) Cs r ε n| ≤ (1 / N : ℝ) * ∑ i, (peak (Cs i) E + η * L1 (Cs i)) := by
  unfold aggH
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_mul, abs_of_pos (by positivity)]
  gcongr
  exact (abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun i _ => unit_le (hs i) hE hr (hε i) n)

/-- **Any mixture of viable-with-margin configurations transfers.** -/
theorem partial_viable (hE : E.Ok) {N : ℕ} (hN : 0 < N) (Cs : Fin N → Cfg) {η : ℝ}
    (hv : ∀ i, Stable (Cs i) E ∧ peak (Cs i) E + η * L1 (Cs i) ≤ E.X)
    {r : Path} (hr : Adm E r) {ε : Fin N → ℕ → ℝ} (hε : ∀ i j, |ε i j| ≤ η) (n : ℕ) :
    |aggH (E := E) Cs r ε n| ≤ E.X := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine (partial_bound hE hN Cs (fun i => (hv i).1) hr hε n).trans ?_
  calc (1 / N : ℝ) * ∑ i, (peak (Cs i) E + η * L1 (Cs i))
      ≤ (1 / N : ℝ) * ∑ _i : Fin N, E.X := by gcongr with i; exact (hv i).2
    _ = E.X := by simp; field_simp

/-- The resonant shock pattern of length `6m`. -/
noncomputable def resPath (E : Env) (m : ℕ) : Path :=
  ⟨0, 0, 0, fun j => E.D * (if 0 ≤ hd 1 (6 * m - 1 - j) then 1 else -1)⟩

theorem resPath_adm (hE : E.Ok) (m : ℕ) : Adm E (resPath E m) := by
  have a0 : |(0 : ℝ)| ≤ E.Θ := by simpa using hE.Θ_nn
  refine ⟨a0, a0, fun j => ?_⟩
  simp only [resPath]
  split_ifs <;> simp [abs_of_pos hE.D_pos]

theorem res_theta (m j : ℕ) : theta E (resPath E m) j = 0 := by
  unfold theta resPath; split_ifs <;> rfl

theorem res_mem (C : Cfg) (m j : ℕ) : mem C E (resPath E m) j = 0 := by
  unfold mem resPath; split_ifs <;> rfl

/-- On the resonant path an unbraked delayed unit reaches exactly `sfac·D·4m` at time `6m`. -/
theorem res_traj {C : Cfg} (hB : C.B = false) (hd' : E.delay = true) (m : ℕ) :
    traj C E (resPath E m) (6 * m) = sfac C E * E.D * (4 * m) := by
  unfold traj; rw [xC_conv]
  have : ∀ t ∈ range (6 * m), h C E t * wres C E (resPath E m) (6 * m - 1 - t) =
      sfac C E * E.D * |hd 1 t| := by
    intro t ht
    rw [mem_range] at ht
    rw [h_nB_delay hB hd']
    simp only [wres, res_theta, res_mem, sub_zero, zero_add]
    simp only [resPath, show 6 * m - 1 - (6 * m - 1 - t) = t by omega]
    split_ifs <;> first
      | (rw [abs_of_nonneg (by assumption)]; ring)
      | (rw [abs_of_neg (by push_neg at *; assumption)]; ring)
      | ring
  rw [sum_congr rfl this, ← mul_sum, hd_one_abs_sum]

/-- **Partial Brake ablation breaks transfer (worst case).** Under delay, one unbraked unit out
of `N` lets an admissible shared realisation push the aggregate past any bound, even with no
idiosyncratic error. -/
theorem partial_unstable (hE : E.Ok) (hd' : E.delay = true) {N : ℕ} (Cs : Fin N → Cfg)
    (i0 : Fin N) (hB0 : (Cs i0).B = false) (X : ℝ) :
    ∃ r, Adm E r ∧ ∃ n, X < aggH (E := E) Cs r (fun _ _ => 0) n := by
  have hN : 0 < N := Fin.pos i0
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set P : ℝ := ∑ i, |peak (Cs i) E|
  have hc := sfac_pos (C := Cs i0) hE
  have hD := hE.D_pos
  obtain ⟨m, hm⟩ := exists_nat_gt ((N * X + P) / (4 * (sfac (Cs i0) E * E.D)))
  refine ⟨resPath E m, resPath_adm hE m, 6 * m, ?_⟩
  set a : Fin N → ℝ := fun i => traj (Cs i) E (resPath E m) (6 * m)
  have ha : aggH (E := E) Cs (resPath E m) (fun _ _ => 0) (6 * m) = (1 / N : ℝ) * ∑ i, a i := by
    unfold aggH; simp only [add_zero]; rfl
  have lower : ∀ i, -|peak (Cs i) E| ≤ a i := by
    intro i
    cases hb : (Cs i).B
    · have := res_traj (E := E) hb hd' m
      simp only [a, this]
      have := sfac_pos (C := Cs i) hE
      have : 0 ≤ sfac (Cs i) E * E.D * (4 * m) := by positivity
      linarith [abs_nonneg (peak (Cs i) E)]
    · have hs : Stable (Cs i) E := Or.inl hb
      have := (abs_le.1 (traj_le hs hE (resPath_adm hE m) (6 * m))).1
      linarith [le_abs_self (peak (Cs i) E)]
  have hi0 : a i0 = sfac (Cs i0) E * E.D * (4 * m) := res_traj hB0 hd' m
  have split := add_sum_erase (univ : Finset (Fin N)) a (mem_univ i0)
  have rest : -P ≤ ∑ i ∈ univ.erase i0, a i := by
    calc -P = ∑ i, -|peak (Cs i) E| := by simp [P]
      _ ≤ ∑ i ∈ univ.erase i0, -|peak (Cs i) E| :=
          sum_le_sum_of_subset_of_nonpos (erase_subset _ _) (fun i _ _ => by
            simp only [Left.neg_nonpos_iff]; exact abs_nonneg _)
      _ ≤ ∑ i ∈ univ.erase i0, a i := sum_le_sum fun i _ => lower i
  rw [div_lt_iff₀ (by positivity)] at hm
  rw [ha, one_div, inv_mul_eq_div, lt_div_iff₀ hN', ← split, hi0]
  nlinarith

/-! ### 2. Adaptation -/

theorem adapt_exact {C : Cfg} (hM : C.M = true) (hW : C.W = true) (hsh : E.shift = true)
    {r : Path} {j : ℕ} (hj : r.s0 ≤ j) :
    theta E r j - mem C E r j = 0 ↔ (r.s0 + lat C E ≤ j ∨ r.θ1 = r.θ0) := by
  have ht : theta E r j = r.θ1 := by simp [theta, hsh, hj]
  rw [ht]
  by_cases h : r.s0 + lat C E ≤ j
  · simp [mem, hM, hW, hsh, h]
  · simp only [mem, hM, hW, hsh, h, true_and, and_false, ite_false, ite_true, false_or]
    exact sub_eq_zero

theorem no_adapt_without_watcher {C : Cfg} (hM : C.M = true) (hW : C.W = false)
    (hsh : E.shift = true) {r : Path} {j : ℕ} (hj : r.s0 ≤ j) :
    theta E r j - mem C E r j = r.θ1 - r.θ0 := by
  simp [theta, mem, hM, hW, hsh, hj]

theorem no_baseline_without_memory {C : Cfg} (hM : C.M = false) (r : Path) (j : ℕ) :
    theta E r j - mem C E r j = theta E r j := by
  simp [mem, hM]

/-! ### 3. Resistance to destabilising feedback (undelayed loop) -/

theorem resist_iff {k δ : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) (hδ : 0 ≤ δ) :
    (∃ B : ℝ, ∀ n, ∑ t ∈ range n, |(1 - (k - δ)) ^ t| ≤ B) ↔ δ < k := by
  set q := 1 - (k - δ)
  have hq0 : 0 ≤ q := by simp only [q]; linarith
  constructor
  · rintro ⟨B, hB⟩
    by_contra hlt
    push_neg at hlt
    have hq1 : 1 ≤ q := by simp only [q]; linarith
    obtain ⟨n, hn⟩ := exists_nat_gt B
    have : (n : ℝ) ≤ ∑ t ∈ range n, |q ^ t| := by
      calc (n : ℝ) = ∑ _t ∈ range n, (1 : ℝ) := by simp
        _ ≤ _ := sum_le_sum fun t _ => by
          rw [abs_of_nonneg (pow_nonneg hq0 t)]; exact one_le_pow₀ hq1
    linarith [hB n]
  · intro hlt
    have hq1 : q < 1 := by simp only [q]; linarith
    refine ⟨1 / (1 - q), fun n => ?_⟩
    simp_rw [abs_of_nonneg (pow_nonneg hq0 _)]
    rw [geom_sum_eq hq1.ne, div_eq_mul_inv, one_div]
    have h1 : 0 < 1 - q := by linarith
    have : q ^ n - 1 = -(1 - q ^ n) := by ring
    rw [this, show q - 1 = -(1 - q) by ring, neg_mul, inv_neg, mul_neg, neg_neg]
    calc (1 - q ^ n) * (1 - q)⁻¹ ≤ 1 * (1 - q)⁻¹ := by
          gcongr; linarith [pow_nonneg hq0 n]
      _ = (1 - q)⁻¹ := one_mul _

/-- **The Brake costs feedback margin without delay.** Effective gain `gain C − δ`. -/
theorem brake_resistance_nodelay {C : Cfg} {δ : ℝ} (hδ : 0 ≤ δ) :
    (∃ B : ℝ, ∀ n, ∑ t ∈ range n, |(1 - (gain C - δ)) ^ t| ≤ B) ↔
      δ < (if C.B then 1 / 4 else 1) := by
  unfold gain
  split_ifs <;> exact resist_iff (by norm_num) (by norm_num) hδ

/-- The undelayed perturbed loop `x' = (1 − k)x + δx + w` is `xa (k − δ)`. -/
theorem perturbed_loop (k δ : ℝ) (w : ℕ → ℝ) (n : ℕ) :
    xa (k - δ) w (n + 1) = (1 - k) * xa (k - δ) w n + δ * xa (k - δ) w n + w n := by
  simp only [xa]; ring

end FiveOrgans.CoupledPartial
