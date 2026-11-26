import FiveOrgans.KnownStart

/-!
# The data-rate theorem (worst-case, uniform form)

Noise-free version of the `SensingRate` world: `x' = a x + u`, one of `M` messages per step, causal
strategies `SensingRate.Strat`, start unknown in `[-r, r]`.

* `radius_lower`: for every strategy and every horizon `N`, if all starts end within `ε` of the
  origin at time `N`, then `r |a|^N ≤ ε M^N`. The worst-case radius can shrink by at most a factor
  `|a| / M` per step.
* `zoom`: a zooming strategy attains this: every start is within `r (|a|/M)^N` at time `N`.
* `stabilise_iff`: some strategy drives every start uniformly to the origin
  (`∀ ε > 0, ∃ N, ∀ start, ∀ n ≥ N, |x n| ≤ ε`) iff **`|a| < M`**, i.e. `log₂ M > log₂ |a|` bits
  per step: the data-rate theorem of Nair–Evans / Tatikonda–Mitter in its scalar worst-case form.

Scope. Scalar, linear, noise-free, unlimited actuation, no delay, uniform convergence over the start
interval. The pointwise (non-uniform) and stochastic versions are not proved here. As everywhere in
this repository, this is a statement about the model.
-/

namespace FiveOrgans.DataRate
open FiveOrgans.SensingRate MeasureTheory Set Filter

variable {M : ℕ} {a r : ℝ}

/-- No disturbance. -/
def z : ℕ → ℝ := fun _ => 0

theorem len (S : Strat M) (x₀ : ℝ) (w : ℕ → ℝ) :
    ∀ n, (hist a S x₀ w n).1.length = n + 1 ∧ (hist a S x₀ w n).2.length = n + 1
  | 0 => by simp [hist]
  | n + 1 => by
    have := len S x₀ w n
    simp [hist, this.1, this.2]

/-- Starts that receive the same messages up to step `n` separate by the factor `a^(n+1)`. -/
theorem diff (S : Strat M) (x₀ y₀ : ℝ) : ∀ n, (hist a S x₀ z n).2 = (hist a S y₀ z n).2 →
    st a S x₀ z (n + 1) - st a S y₀ z (n + 1) = a ^ (n + 1) * (x₀ - y₀)
  | 0, h => by
    have e1 : st a S x₀ z 1 = a * x₀ + S.act (hist a S x₀ z 0).2 + 0 := rfl
    have e2 : st a S y₀ z 1 = a * y₀ + S.act (hist a S y₀ z 0).2 + 0 := rfl
    rw [e1, e2, h]; ring
  | n + 1, h => by
    have h' : (hist a S x₀ z n).2 = (hist a S y₀ z n).2 := congrArg List.tail h
    have ih := diff S x₀ y₀ n h'
    have e1 : st a S x₀ z (n + 2) = a * st a S x₀ z (n + 1) + S.act (hist a S x₀ z (n + 1)).2 + 0 :=
      rfl
    have e2 : st a S y₀ z (n + 2) = a * st a S y₀ z (n + 1) + S.act (hist a S y₀ z (n + 1)).2 + 0 :=
      rfl
    rw [e1, e2, h]
    linear_combination a * ih

/-- **Lower bound on the worst-case radius.** -/
theorem radius_lower (hr : 0 ≤ r) (S : Strat M) (N : ℕ) {ε : ℝ}
    (h : ∀ x₀, |x₀| ≤ r → |st a S x₀ z N| ≤ ε) : r * |a| ^ N ≤ ε * M ^ N := by
  cases N with
  | zero =>
    have := h r (by rw [abs_of_nonneg hr])
    simp only [st, hist, List.headD_cons] at this
    rw [abs_of_nonneg hr] at this; simpa using this
  | succ n =>
  rcases eq_or_ne a 0 with ha | ha
  · have : 0 ≤ ε := (abs_nonneg _).trans (h 0 (by simpa using hr))
    rw [ha]; simp; positivity
  have hp : 0 < |a| ^ (n + 1) := pow_pos (abs_pos.2 ha) _
  have hε : 0 ≤ ε := (abs_nonneg _).trans (h 0 (by simpa using hr))
  set δ := 2 * ε / |a| ^ (n + 1) with hδ
  let code : ℝ → List.Vector (Fin M) (n + 1) := fun x => ⟨(hist a S x z n).2, (len S x z n).2⟩
  let F : List.Vector (Fin M) (n + 1) → Set ℝ := fun v => {x | |x| ≤ r ∧ code x = v}
  have hF : ∀ v, volume (F v) ≤ ENNReal.ofReal δ := by
    intro v
    refine (Real.volume_le_diam _).trans (Metric.ediam_le fun x hx y hy => ?_)
    rw [edist_dist, Real.dist_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    have hc : (hist a S x z n).2 = (hist a S y z n).2 :=
      congrArg Subtype.val (hx.2.trans hy.2.symm)
    have e := diff S x y n hc
    have hb : |a ^ (n + 1) * (x - y)| ≤ 2 * ε := by
      rw [← e]
      calc _ ≤ |st a S x z (n + 1)| + |st a S y z (n + 1)| := abs_sub _ _
        _ ≤ 2 * ε := by linarith [h x hx.1, h y hy.1]
    rw [abs_mul, abs_pow] at hb
    rw [hδ, le_div_iff₀ hp]; linarith
  have hsub : Icc (-r) r ⊆ ⋃ v, F v := fun x hx =>
    mem_iUnion.2 ⟨code x, abs_le.2 ⟨hx.1, hx.2⟩, rfl⟩
  have hv : ENNReal.ofReal (2 * r) ≤ ENNReal.ofReal (M ^ (n + 1) * δ) := by
    calc ENNReal.ofReal (2 * r) = volume (Icc (-r) r) := by
          rw [Real.volume_Icc]; congr 1; ring
      _ ≤ volume (⋃ v, F v) := measure_mono hsub
      _ ≤ ∑ v, volume (F v) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _v : List.Vector (Fin M) (n + 1), ENNReal.ofReal δ := Finset.sum_le_sum fun v _ => hF v
      _ = ENNReal.ofReal (M ^ (n + 1) * δ) := by
          rw [Finset.sum_const, Finset.card_univ, card_vector, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (Nat.cast_nonneg M),
            ENNReal.ofReal_natCast, Nat.cast_pow]
  have hfin : 2 * r ≤ M ^ (n + 1) * δ :=
    (ENNReal.ofReal_le_ofReal_iff (by rw [hδ]; positivity)).1 hv
  rw [hδ, mul_div_assoc', le_div_iff₀ hp] at hfin
  linarith

/-- Radius of the box known at step `k`. -/
noncomputable def R (M : ℕ) (a r : ℝ) (k : ℕ) : ℝ := r * (|a| / M) ^ k

theorem R_pos (hM : 0 < M) (ha : a ≠ 0) (hr : 0 < r) (k : ℕ) : 0 < R M a r k := by
  have : (0 : ℝ) < M := by exact_mod_cast hM
  unfold R; have := abs_pos.2 ha; positivity

/-- The zooming strategy: at step `k` quantise the box of radius `R k` into `M` cells. -/
noncomputable def zoomS (hM : 0 < M) (ha : a ≠ 0) (hr : 0 < r) : Strat M :=
  ⟨fun l => cell hM (R_pos hM ha hr (l.length - 1)) (l.headD 0),
   fun l => -(a * centre M (R M a r (l.length - 1)) (l.headD ⟨0, hM⟩))⟩

/-- **Upper bound.** The zooming strategy attains the radius `r (|a|/M)^N`. -/
theorem zoom (hM : 0 < M) (ha : a ≠ 0) (hr : 0 < r) {x₀ : ℝ} (hx : |x₀| ≤ r) :
    ∀ n, |st a (zoomS hM ha hr) x₀ z n| ≤ R M a r n
  | 0 => by simpa [st, hist, R] using hx
  | n + 1 => by
    have ih := zoom hM ha hr hx n
    set S := zoomS hM ha hr
    have hl := len (a := a) S x₀ z n
    have hm : ∃ t, (hist a S x₀ z n).2 = S.enc (hist a S x₀ z n).1 :: t := by
      cases n with
      | zero => exact ⟨[], rfl⟩
      | succ n => exact ⟨_, rfl⟩
    obtain ⟨t, ht⟩ := hm
    have henc : S.enc (hist a S x₀ z n).1 = cell hM (R_pos hM ha hr n) (st a S x₀ z n) := by
      show cell hM (R_pos hM ha hr ((hist a S x₀ z n).1.length - 1)) _ = _
      simp only [hl.1, Nat.add_sub_cancel]; rfl
    have hact : S.act (hist a S x₀ z n).2 =
        -(a * centre M (R M a r n) (cell hM (R_pos hM ha hr n) (st a S x₀ z n))) := by
      show -(a * centre M (R M a r ((hist a S x₀ z n).2.length - 1)) _) = _
      rw [hl.2, Nat.add_sub_cancel, ht, henc]; rfl
    have e : st a S x₀ z (n + 1) = a * st a S x₀ z n + S.act (hist a S x₀ z n).2 + 0 := rfl
    rw [e, hact]
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    have hc := cell_spec hM (R_pos hM ha hr n) ih
    calc |a * st a S x₀ z n + -(a * centre M (R M a r n) (cell hM (R_pos hM ha hr n)
            (st a S x₀ z n))) + 0|
          = |a| * |st a S x₀ z n - centre M (R M a r n) (cell hM (R_pos hM ha hr n)
            (st a S x₀ z n))| := by rw [← abs_mul]; congr 1; ring
      _ ≤ |a| * (R M a r n / M) := mul_le_mul_of_nonneg_left hc (abs_nonneg a)
      _ = R M a r (n + 1) := by unfold R; rw [pow_succ]; field_simp

/-- Uniform stabilisation of every start in `[-r, r]`. -/
def Stabilises (a r : ℝ) (S : Strat M) : Prop :=
  ∀ ε > 0, ∃ N, ∀ x₀, |x₀| ≤ r → ∀ n ≥ N, |st a S x₀ z n| ≤ ε

/-- **The data-rate theorem (scalar, worst-case, uniform).** -/
theorem stabilise_iff (hM : 0 < M) (ha : a ≠ 0) (hr : 0 < r) :
    (∃ S : Strat M, Stabilises a r S) ↔ |a| < M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have ha' : 0 < |a| := abs_pos.2 ha
  constructor
  · rintro ⟨S, hS⟩
    by_contra hc; push Not at hc
    obtain ⟨N, hN⟩ := hS (r / 2) (by positivity)
    have hl := radius_lower hr.le S N fun x₀ hx => hN x₀ hx N le_rfl
    have : (M : ℝ) ^ N ≤ |a| ^ N := pow_le_pow_left₀ hM'.le hc N
    have : 0 < |a| ^ N := pow_pos ha' N
    nlinarith
  · intro hlt
    refine ⟨zoomS hM ha hr, fun ε hε => ?_⟩
    have hq0 : 0 ≤ |a| / M := by positivity
    have hq1 : |a| / M < 1 := (div_lt_one hM').2 hlt
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hr) hq1
    refine ⟨N, fun x₀ hx n hn => (zoom hM ha hr hx n).trans ?_⟩
    unfold R
    have : (|a| / M) ^ n ≤ (|a| / M) ^ N := pow_le_pow_of_le_one hq0 hq1.le hn
    have : r * (|a| / M) ^ N < ε := by rw [lt_div_iff₀ hr] at hN; linarith
    nlinarith

end FiveOrgans.DataRate
