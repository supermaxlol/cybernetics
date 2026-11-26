import FiveOrgans.ControlEntropy

/-!
# What a cue is worth for growth, and when the information bound fails

Environment `x` and cue `y` with joint distribution `J x y`. Phenotype `σ` grows by `f σ x` in
environment `x`. A strategy `θ y σ` is the fraction of a population taking phenotype `σ` on cue
`y`. Long-run growth per generation in an i.i.d. environment is the expected **log** of mean growth.

* `value_le_mi`: for every cue strategy `θ` that survives, there is a blind strategy that is at
  most `I(X;Y)` worse. This holds for **any** growth matrix (no diagonality needed).
* `kelly_blind`, `kelly_cue`, `kelly_value_eq`: with diagonal growth (one viable phenotype per
  environment), conditional betting beats **every** surviving blind strategy by at least `I(X;Y)`,
  so with `value_le_mi` the value is exactly `I(X;Y)`.
* `indiv_eq`, `indiv_value_le`: if each individual gets its **own** noisy copy `y` of a shared cue
  `z` (kernel `q z y`), the population behaves like one with the shared cue `z` and blurred
  strategy, so the value is at most `I(X;Z)`.
* `indiv_beats_mi`: that value can **exceed** `I(X;Y)`, the information any individual has. Fair
  binary environment, individual error `1/4`: value `log (3/2)`, information `(3/4) log 3 − log 2`.
  So `value ≤ I(individual signal; environment)` is **false** for a population with independent
  individual noise.

Survival is required explicitly. In Lean `log 0 = 0`, so without the positivity hypotheses
extinction would be scored as "no growth" and the theorems would be wrong.

Sources: Kelly 1956; Bergstrom and Lachmann (arXiv q-bio/0510007); Rivoire and Leibler, J. Stat. Phys.
142 (2011) 1124 (Eqs. 45–46, 48). Scope: i.i.d. environments, finite sets, no inheritance, infinite
population (no demographic noise). That expected log growth is the almost-sure long-run rate is
the standard law-of-large-numbers statement and is not proved here.
-/

namespace FiveOrgans.GrowthValue
open FiveOrgans.CompressionInfo FiveOrgans.ControlEntropy Finset Real

variable {X Y Z S : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype S]

/-- Mean growth in environment `x` of a population with phenotype fractions `b`. -/
noncomputable def mean (f : S → X → ℝ) (b : S → ℝ) (x : X) : ℝ := ∑ σ, f σ x * b σ

/-- Expected log growth with cue strategy `θ`. -/
noncomputable def growth (J : X → Y → ℝ) (f : S → X → ℝ) (θ : Y → S → ℝ) : ℝ :=
  ∑ x, ∑ y, J x y * log (mean f (θ y) x)

/-- Expected log growth of a blind strategy. -/
noncomputable def blind (J : X → Y → ℝ) (f : S → X → ℝ) (b : S → ℝ) : ℝ :=
  ∑ x, mX J x * log (mean f b x)

/-- Blind strategy that ignores the cue but keeps the same overall mixture. -/
noncomputable def mix (J : X → Y → ℝ) (θ : Y → S → ℝ) (σ : S) : ℝ := ∑ y, mC J y * θ y σ

variable {J : X → Y → ℝ} {f : S → X → ℝ} {θ : Y → S → ℝ}

theorem mi_eq :
    mi J = ∑ x, ∑ y, J x y * (log (J x y) - log (mX J x) - log (mC J y)) := by
  have e1 : ent (mX J) = ∑ x, ∑ y, -(J x y * log (mX J x)) := by
    unfold ent; refine sum_congr rfl fun x _ => ?_
    rw [sum_neg_distrib, ← sum_mul]; rfl
  have e2 : ent (mC J) = ∑ x, ∑ y, -(J x y * log (mC J y)) := by
    rw [sum_comm]; unfold ent; refine sum_congr rfl fun y _ => ?_
    rw [sum_neg_distrib, ← sum_mul]; rfl
  have e3 : entJ J = ∑ x, ∑ y, -(J x y * log (J x y)) := by
    unfold entJ negMulLog; rw [sum_comm]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
  unfold mi; rw [e1, e2, e3, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_add_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun y _ => by ring

theorem mix_mean (x : X) : mean f (mix J θ) x = ∑ y, mC J y * mean f (θ y) x := by
  unfold mean mix
  simp only [mul_sum]; rw [sum_comm]
  exact sum_congr rfl fun y _ => sum_congr rfl fun σ _ => by ring

theorem J_le_mC (hJ : ∀ x y, 0 ≤ J x y) (x : X) (y : Y) : J x y ≤ mC J y :=
  single_le_sum (f := fun x => J x y) (fun x _ => hJ x y) (mem_univ x)

theorem J_le_mX (hJ : ∀ x y, 0 ≤ J x y) (x : X) (y : Y) : J x y ≤ mX J x :=
  single_le_sum (f := fun y => J x y) (fun y _ => hJ x y) (mem_univ y)

theorem mix_dist (hJ : ∀ x y, 0 ≤ J x y) (h1 : ∑ x, ∑ y, J x y = 1) (hθ : ∀ y σ, 0 ≤ θ y σ)
    (hθ1 : ∀ y, ∑ σ, θ y σ = 1) : (∀ σ, 0 ≤ mix J θ σ) ∧ ∑ σ, mix J θ σ = 1 := by
  refine ⟨fun σ => sum_nonneg fun y _ => mul_nonneg (mC_nonneg hJ y) (hθ y σ), ?_⟩
  unfold mix; rw [sum_comm, ← mC_sum h1]
  exact sum_congr rfl fun y _ => by rw [← mul_sum, hθ1, mul_one]

theorem mix_survives (hJ : ∀ x y, 0 ≤ J x y) (hf : ∀ σ x, 0 ≤ f σ x) (hθ : ∀ y σ, 0 ≤ θ y σ)
    (hs : ∀ x y, 0 < J x y → 0 < mean f (θ y) x) {x : X} {y : Y} (h : 0 < J x y) :
    0 < mean f (mix J θ) x := by
  rw [mix_mean]
  have hm : ∀ y, 0 ≤ mean f (θ y) x := fun y => sum_nonneg fun σ _ => mul_nonneg (hf σ x) (hθ y σ)
  exact (mul_pos (h.trans_le (J_le_mC hJ x y)) (hs x y h)).trans_le
    (single_le_sum (f := fun y => mC J y * mean f (θ y) x)
      (fun y _ => mul_nonneg (mC_nonneg hJ y) (hm y)) (mem_univ y))

/-- **The growth value of a shared cue is at most its mutual information**, for any growth
matrix: the blind mixture of a surviving cue strategy survives and is at most `I(X;Y)` worse. -/
theorem value_le_mi (hJ : ∀ x y, 0 ≤ J x y) (hf : ∀ σ x, 0 ≤ f σ x)
    (hθ : ∀ y σ, 0 ≤ θ y σ) (hs : ∀ x y, 0 < J x y → 0 < mean f (θ y) x) :
    growth J f θ ≤ blind J f (mix J θ) + mi J := by
  rw [mi_eq]
  have hb : blind J f (mix J θ) = ∑ x, ∑ y, J x y * log (mean f (mix J θ) x) := by
    unfold blind; exact sum_congr rfl fun x _ => by rw [← sum_mul]; rfl
  rw [hb, ← sum_add_distrib]
  unfold growth
  have hm : ∀ x y, 0 ≤ mean f (θ y) x := fun x y =>
    sum_nonneg fun σ _ => mul_nonneg (hf σ x) (hθ y σ)
  refine sum_le_sum fun x _ => ?_
  rw [← sum_add_distrib]
  have hX0 : 0 ≤ mX J x := sum_nonneg fun y _ => hJ x y
  rcases hX0.eq_or_lt with h0 | hX
  · have : ∀ y, J x y = 0 := fun y =>
      (sum_eq_zero_iff_of_nonneg fun y _ => hJ x y).1 h0.symm y (mem_univ y)
    simp [this]
  -- some y has positive mass, so the blind mixture survives in x
  have hF : 0 < mean f (mix J θ) x := by
    obtain ⟨y, _, hy⟩ := exists_lt_of_sum_lt (s := univ) (f := fun _ : Y => (0 : ℝ))
      (g := fun y => J x y) (by rw [sum_const_zero]; exact hX)
    exact mix_survives hJ hf hθ hs hy
  have term : ∀ y, J x y * log (mean f (θ y) x) -
      (J x y * log (mean f (mix J θ) x) +
        J x y * (log (J x y) - log (mX J x) - log (mC J y))) ≤
      mX J x * (mC J y * mean f (θ y) x / mean f (mix J θ) x) - J x y := by
    intro y
    rcases (hJ x y).eq_or_lt with h | h
    · rw [← h]; simp
      exact mul_nonneg hX.le (div_nonneg (mul_nonneg (mC_nonneg hJ y) (hm x y)) hF.le)
    · have hC := h.trans_le (J_le_mC hJ x y)
      have hp := hs x y h
      have hpos : 0 < mX J x * mC J y * mean f (θ y) x / (mean f (mix J θ) x * J x y) := by
        positivity
      have hl := log_le_sub_one_of_pos hpos
      rw [log_div (by positivity) (by positivity), log_mul (by positivity) hp.ne',
        log_mul hX.ne' hC.ne', log_mul hF.ne' h.ne'] at hl
      have hh := mul_le_mul_of_nonneg_left hl h.le
      have e : J x y * (mX J x * mC J y * mean f (θ y) x / (mean f (mix J θ) x * J x y) - 1)
          = mX J x * (mC J y * mean f (θ y) x / mean f (mix J θ) x) - J x y := by
        field_simp
      rw [e] at hh
      linarith
  have hsum := sum_le_sum fun y (_ : y ∈ (univ : Finset Y)) => term y
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← sum_div, ← mix_mean, div_self hF.ne',
    mul_one] at hsum
  have : ∑ y, J x y = mX J x := rfl
  linarith

/-! ### Diagonal growth: the value is exactly the mutual information -/

section Kelly
variable [DecidableEq X]

/-- Diagonal growth: only phenotype `x` survives environment `x`, growing by `g x`. -/
def diag (g : X → ℝ) (σ x : X) : ℝ := if σ = x then g x else 0

theorem mean_diag (g : X → ℝ) (b : X → ℝ) (x : X) : mean (diag g) b x = g x * b x := by
  simp [mean, diag]

/-- Conditional ("Bayesian") betting. -/
noncomputable def bayes (J : X → Y → ℝ) (y : Y) (x : X) : ℝ := J x y / mC J y

/-- Among surviving blind strategies, betting the environment's frequencies is best. -/
theorem kelly_blind {J : X → Y → ℝ} (hJ : ∀ x y, 0 ≤ J x y) (h1 : ∑ x, ∑ y, J x y = 1)
    {g : X → ℝ} (hg : ∀ x, 0 < g x) {b : X → ℝ} (hb : ∀ x, 0 ≤ b x) (hb1 : ∑ x, b x = 1)
    (hs : ∀ x, 0 < mX J x → 0 < b x) :
    blind J (diag g) b ≤ blind J (diag g) (mX J) := by
  unfold blind
  have term : ∀ x, mX J x * log (mean (diag g) b x) - mX J x * log (mean (diag g) (mX J) x)
      ≤ b x - mX J x := by
    intro x
    rw [mean_diag, mean_diag]
    have hX0 : 0 ≤ mX J x := sum_nonneg fun y _ => hJ x y
    rcases hX0.eq_or_lt with h | h
    · rw [← h]; simpa using hb x
    · have hbx := hs x h
      rw [log_mul (hg x).ne' hbx.ne', log_mul (hg x).ne' h.ne']
      have hl := log_le_sub_one_of_pos (div_pos hbx h)
      rw [log_div hbx.ne' h.ne'] at hl
      have hh := mul_le_mul_of_nonneg_left hl h.le
      have e : mX J x * (b x / mX J x - 1) = b x - mX J x := by field_simp
      rw [e] at hh; linarith
  have hsum := sum_le_sum fun x (_ : x ∈ (univ : Finset X)) => term x
  rw [sum_sub_distrib, sum_sub_distrib, hb1] at hsum
  have : ∑ x, mX J x = 1 := h1
  linarith

/-- Conditional betting gains exactly `I(X;Y)` over the best blind bet. -/
theorem kelly_cue {J : X → Y → ℝ} (hJ : ∀ x y, 0 ≤ J x y) {g : X → ℝ} (hg : ∀ x, 0 < g x) :
    growth J (diag g) (bayes J) = blind J (diag g) (mX J) + mi J := by
  rw [mi_eq]
  have hb : blind J (diag g) (mX J) = ∑ x, ∑ y, J x y * log (mean (diag g) (mX J) x) := by
    unfold blind; exact sum_congr rfl fun x _ => by rw [← sum_mul]; rfl
  rw [hb, ← sum_add_distrib]; unfold growth
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  rcases (hJ x y).eq_or_lt with h | h
  · rw [← h]; simp
  · have hC := h.trans_le (J_le_mC hJ x y)
    have hX := h.trans_le (J_le_mX hJ x y)
    rw [mean_diag, mean_diag, bayes, log_mul (hg x).ne' (div_pos h hC).ne',
      log_div h.ne' hC.ne', log_mul (hg x).ne' hX.ne']
    ring

/-- **Kelly: the value of a shared cue is exactly `I(X;Y)`.** No surviving cue strategy beats the
best blind bet by more, and conditional betting attains it. -/
theorem kelly_value_eq {J : X → Y → ℝ} (hJ : ∀ x y, 0 ≤ J x y) (h1 : ∑ x, ∑ y, J x y = 1)
    {g : X → ℝ} (hg : ∀ x, 0 < g x) :
    growth J (diag g) (bayes J) - blind J (diag g) (mX J) = mi J ∧
    ∀ θ : Y → X → ℝ, (∀ y σ, 0 ≤ θ y σ) → (∀ y, ∑ σ, θ y σ = 1) →
      (∀ x y, 0 < J x y → 0 < θ y x) →
      growth J (diag g) θ - blind J (diag g) (mX J) ≤ mi J := by
  refine ⟨by rw [kelly_cue hJ hg]; ring, fun θ hθ hθ1 hs => ?_⟩
  have hd : ∀ σ x, 0 ≤ diag g σ x := fun σ x => by unfold diag; split_ifs <;> simp [(hg x).le]
  have hs' : ∀ x y, 0 < J x y → 0 < mean (diag g) (θ y) x := fun x y h => by
    rw [mean_diag]; exact mul_pos (hg x) (hs x y h)
  have a := value_le_mi hJ hd hθ hs'
  obtain ⟨hb, hb1⟩ := mix_dist hJ h1 hθ hθ1
  have c := kelly_blind hJ h1 hg hb hb1 fun x hx => by
    obtain ⟨y, _, hy⟩ := exists_lt_of_sum_lt (s := univ) (f := fun _ : Y => (0 : ℝ))
      (g := fun y => J x y) (by rw [sum_const_zero]; exact hx)
    have := mix_survives hJ hd hθ hs' hy
    rw [mean_diag] at this
    exact (pos_iff_pos_of_mul_pos this).1 (hg x)
  linarith

end Kelly

/-! ### Independent individual signals -/

/-- Growth when each individual receives its own copy `y ∼ q z ·` of the shared cue `z`. -/
noncomputable def indiv (J : X → Z → ℝ) (q : Z → Y → ℝ) (f : S → X → ℝ) (θ : Y → S → ℝ) : ℝ :=
  ∑ x, ∑ z, J x z * log (∑ y, q z y * mean f (θ y) x)

/-- Strategy seen at population level. -/
noncomputable def blur (q : Z → Y → ℝ) (θ : Y → S → ℝ) (z : Z) (σ : S) : ℝ :=
  ∑ y, q z y * θ y σ

theorem indiv_eq (J : X → Z → ℝ) (q : Z → Y → ℝ) (f : S → X → ℝ) (θ : Y → S → ℝ) :
    indiv J q f θ = growth J f (blur q θ) := by
  unfold indiv growth mean blur
  refine sum_congr rfl fun x _ => sum_congr rfl fun z _ => ?_
  congr 2
  simp only [mul_sum]; rw [sum_comm]
  exact sum_congr rfl fun σ _ => sum_congr rfl fun y _ => by ring

/-- **With individual signals the value is bounded by the information in the shared cue.** -/
theorem indiv_value_le {J : X → Z → ℝ} (hJ : ∀ x z, 0 ≤ J x z) {q : Z → Y → ℝ}
    (hq : ∀ z y, 0 ≤ q z y) (hf : ∀ σ x, 0 ≤ f σ x) (hθ : ∀ y σ, 0 ≤ θ y σ)
    (hs : ∀ x z, 0 < J x z → 0 < mean f (blur q θ z) x) :
    indiv J q f θ ≤ blind J f (mix J (blur q θ)) + mi J := by
  rw [indiv_eq]
  exact value_le_mi hJ hf (fun z σ => sum_nonneg fun y _ => mul_nonneg (hq z y) (hθ y σ)) hs

/-- Perfectly shared fair bit. -/
noncomputable def Jz (x z : Bool) : ℝ := if x = z then 1 / 2 else 0

/-- Individual reading with error `1/4`. -/
noncomputable def q4 (z y : Bool) : ℝ := if y = z then 3 / 4 else 1 / 4

/-- Joint law of environment and one individual's reading. -/
noncomputable def Jxy (x y : Bool) : ℝ := if y = x then 3 / 8 else 1 / 8

/-- Follow your own reading. -/
def follow (y σ : Bool) : ℝ := if σ = y then 1 else 0

theorem log_eight : log (8 : ℝ) = 3 * log 2 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]; push_cast; ring

theorem mi_Jxy : mi Jxy = 3 / 4 * log 3 - log 2 := by
  have a : mX Jxy = fun _ => (2⁻¹ : ℝ) := by
    funext x; cases x <;> simp [mX, Jxy] <;> norm_num
  have b : mC Jxy = fun _ => (2⁻¹ : ℝ) := by
    funext x; cases x <;> simp [mC, Jxy] <;> norm_num
  have l1 : log (3 / 8 : ℝ) = log 3 - 3 * log 2 := by
    rw [log_div (by norm_num) (by norm_num), log_eight]
  have l2 : log (1 / 8 : ℝ) = -(3 * log 2) := by rw [one_div, log_inv, log_eight]
  have c : entJ Jxy = 2 * (-(3 / 8 * log (3 / 8)) + -(1 / 8 * log (1 / 8))) := by
    simp only [entJ, Jxy, negMulLog, Fintype.sum_bool]
    simp only [ite_true, Bool.true_eq_false, Bool.false_eq_true, ite_false]; ring
  have e : ent (fun _ : Bool => (2⁻¹ : ℝ)) = log 2 := by simp [ent]
  unfold mi; rw [a, b, c, e, l1, l2]; ring

/-- **The individual-information bound is false.** The joint law `Jxy` is the law of environment
and one individual's reading; following the reading gains `log (3/2)` over the best blind bet, for
every surviving blind bet, and `log (3/2) > I(X;Y)`. -/
theorem indiv_beats_mi :
    (∀ x y, Jxy x y = ∑ z, Jz x z * q4 z y) ∧
    (∀ b : Bool → ℝ, (∀ x, 0 < b x) → ∑ x, b x = 1 →
      log (3 / 2) ≤ indiv Jz q4 (diag fun _ => 1) follow - blind Jz (diag fun _ => 1) b) ∧
    mi Jxy < log (3 / 2) := by
  have hi : indiv Jz q4 (diag fun _ => 1) follow = log (3 / 4) := by
    simp only [indiv, mean_diag, Jz, q4, follow, Fintype.sum_bool]
    norm_num
    ring
  have hX : mX Jz = fun _ => (2⁻¹ : ℝ) := by funext x; cases x <;> simp [mX, Jz]
  refine ⟨fun x y => ?_, fun b hb hb1 => ?_, ?_⟩
  · cases x <;> cases y <;> simp [Jxy, Jz, q4] <;> norm_num
  · have k := kelly_blind (J := Jz) (fun x z => by unfold Jz; split_ifs <;> norm_num)
      (by simp [Jz]; try norm_num) (g := fun _ => 1) (fun _ => one_pos) (fun x => (hb x).le) hb1
      (fun x _ => hb x)
    have hB : blind Jz (diag fun _ => 1) (mX Jz) = -log 2 := by
      rw [hX]; simp [blind, mean_diag, hX]
      try ring
    have l : log (3 / 2 : ℝ) = log (3 / 4) + log 2 := by
      rw [← log_mul (by norm_num) (by norm_num)]; norm_num
    rw [hi, l]; linarith
  · rw [mi_Jxy, log_div (by norm_num) (by norm_num)]
    have := log_pos (by norm_num : (1 : ℝ) < 3)
    linarith

end FiveOrgans.GrowthValue
