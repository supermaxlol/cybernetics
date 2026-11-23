import FiveOrgans.Coupled

/-!
# Complete ablation of the coupled model: all 32 configurations, seven environments

Every table below is an exact `↔` over all `2⁵ = 32` configurations, proved by evaluating
`viable_closed`. For each environment it states exactly which capacity sets survive every
admissible realisation with their resources.

| environment | what it shows | viable configurations |
|---|---|---|
| `calm`          | brake harmful without delay           | `¬B ∨ (S ∧ P)` (20) |
| `delayE`        | brake necessary and sufficient        | `B` (16) |
| `shiftFast`     | M–W complementary, S–P substitutable  | `B ∧ M ∧ W ∧ (S ∨ P)` (3) |
| `shiftSlow`     | slow Watcher: Spotlight necessary     | `B ∧ M ∧ W ∧ P` (2) |
| `deadbeatShift` | memory harmful, brake harmful         | `¬M ∧ ¬B ∧ (S ∨ P)` (6) |
| `hostile`       | all five capacities jointly necessary | `S ∧ M ∧ P ∧ B ∧ W` (1) |
| `poor`          | the resource budget binds             | none (0) |

These are **mathematical** necessity statements about this model under its stated assumptions.
They are not empirical claims about any real system.
- "Necessary" means: no configuration without that capacity is viable in that environment.
- Necessity is environment-relative. `organ_necessity_relative` shows each capacity is
  necessary in some environment and dispensable in another.
-/

namespace FiveOrgans.CoupledAblation
open FiveOrgans.Coupled

/-- Environment template: `σ = α = 1/2`, every capacity costs `1/10`. -/
noncomputable def mk (D Θ X : ℝ) (K : ℕ) (dl sh : Bool) (inc : ℝ) : Env :=
  ⟨D, Θ, X, 1 / 2, 1 / 2, K, dl, sh, inc, 1 / 10, 1 / 10, 1 / 10, 1 / 10, 1 / 10⟩

theorem mk_ok {D Θ X : ℝ} {K : ℕ} {dl sh : Bool} {inc : ℝ} (hD : 0 < D) (hΘ : 0 ≤ Θ)
    (hK : 1 ≤ K) : (mk D Θ X K dl sh inc).Ok :=
  ⟨hD, hΘ, by norm_num [mk], by norm_num [mk], by norm_num [mk], by norm_num [mk], hK⟩

noncomputable def calm : Env := mk 1 0 (3 / 2) 3 false false 1
noncomputable def delayE : Env := mk 1 0 4 3 true false 1
noncomputable def shiftFast : Env := mk 1 1 4 1 true true 1
noncomputable def shiftSlow : Env := mk 1 1 4 4 true true 1
noncomputable def deadbeatShift : Env := mk 1 1 (3 / 2) 3 false true 1
noncomputable def hostile : Env := mk 1 (1 / 4) (7 / 4) 3 true true 1
noncomputable def poor : Env := mk 1 (1 / 4) (7 / 4) 3 true true (4 / 10)

macro "table" c:ident ok:term : tactic => `(tactic| (
  rw [viable_closed $ok]
  rcases $c:ident with ⟨s, m, p, b, w⟩
  cases s <;> cases m <;> cases p <;> cases b <;> cases w <;>
    norm_num [cost, Stable, peakC, sfac, lat, L1, Hc, calm, delayE, shiftFast, shiftSlow,
      deadbeatShift, hostile, poor, mk]))

theorem calm_table (C : Cfg) :
    Viable C calm ↔ (C.B = false ∨ (C.S = true ∧ C.P = true)) := by
  table C (show calm.Ok from mk_ok (by norm_num) (by norm_num) (by norm_num))

theorem delay_table (C : Cfg) : Viable C delayE ↔ C.B = true := by
  table C (show delayE.Ok from mk_ok (by norm_num) (by norm_num) (by norm_num))

theorem shiftFast_table (C : Cfg) :
    Viable C shiftFast ↔
      (C.B = true ∧ C.M = true ∧ C.W = true ∧ (C.S = true ∨ C.P = true)) := by
  table C (show shiftFast.Ok from mk_ok (by norm_num) (by norm_num) (by norm_num))

theorem shiftSlow_table (C : Cfg) :
    Viable C shiftSlow ↔ (C.B = true ∧ C.M = true ∧ C.W = true ∧ C.P = true) := by
  table C (show shiftSlow.Ok from mk_ok (by norm_num) (by norm_num) (by norm_num))

theorem deadbeatShift_table (C : Cfg) :
    Viable C deadbeatShift ↔
      (C.M = false ∧ C.B = false ∧ (C.S = true ∨ C.P = true)) := by
  table C (show deadbeatShift.Ok from mk_ok (by norm_num) (by norm_num) (by norm_num))

theorem hostile_table (C : Cfg) :
    Viable C hostile ↔
      (C.S = true ∧ C.M = true ∧ C.P = true ∧ C.B = true ∧ C.W = true) := by
  table C (show hostile.Ok from mk_ok (by norm_num) (by norm_num) (by norm_num))

theorem poor_table (C : Cfg) : ¬ Viable C poor := by
  have := (show Viable C poor ↔ False by
    table C (show poor.Ok from mk_ok (by norm_num) (by norm_num) (by norm_num)))
  exact this.1

/-! ### Named consequences -/

def full : Cfg := ⟨true, true, true, true, true⟩

/-- **Complementarity (Memory–Watcher)**: each is useless without the other in `shiftFast`. -/
theorem complementary_MW :
    Viable full shiftFast ∧ ¬ Viable { full with M := false } shiftFast ∧
      ¬ Viable { full with W := false } shiftFast := by
  simp [shiftFast_table, full]

/-- **Substitutability (Skin–Spotlight)** in `shiftFast`: either suffices, removing both fails. -/
theorem substitutable_SP :
    Viable { full with S := false } shiftFast ∧ Viable { full with P := false } shiftFast ∧
      ¬ Viable { full with S := false, P := false } shiftFast := by
  simp [shiftFast_table, full]

/-- **Behavioural similarity ≠ mechanism.** Skin and Spotlight attenuate shocks by the same
factor, so they are interchangeable in `shiftFast`. In `shiftSlow` only Spotlight works,
because it alone also shortens the Watcher's latency. -/
theorem similar_not_same :
    Viable { full with P := false } shiftFast ∧ ¬ Viable { full with P := false } shiftSlow ∧
      Viable { full with S := false } shiftSlow := by
  simp [shiftFast_table, shiftSlow_table, full]

/-- **Harm**: adding Memory, or adding a Brake, destroys viability in `deadbeatShift`. -/
theorem harmful_M_B :
    Viable ⟨false, false, true, false, false⟩ deadbeatShift ∧
      ¬ Viable ⟨false, true, true, false, false⟩ deadbeatShift ∧
      ¬ Viable ⟨false, false, true, true, false⟩ deadbeatShift := by
  simp [deadbeatShift_table]

/-- **Viability is not monotone in the capacity set.** -/
theorem not_monotone : ∃ C C' : Cfg, ∃ E : Env,
    (C.S ≤ C'.S ∧ C.M ≤ C'.M ∧ C.P ≤ C'.P ∧ C.B ≤ C'.B ∧ C.W ≤ C'.W) ∧
      Viable C E ∧ ¬ Viable C' E :=
  ⟨⟨false, false, false, false, false⟩, ⟨false, false, false, true, false⟩, calm,
    by decide, by simp [calm_table], by simp [calm_table]⟩

/-- **Necessity is environment-relative.** Every capacity is necessary in `hostile` and
dispensable in `calm`, where the empty configuration is viable. -/
theorem organ_necessity_relative :
    (∀ C : Cfg, Viable C hostile →
      C.S = true ∧ C.M = true ∧ C.P = true ∧ C.B = true ∧ C.W = true) ∧
      Viable ⟨false, false, false, false, false⟩ calm := by
  refine ⟨fun C h => (hostile_table C).1 h, by simp [calm_table]⟩

/-- **Brake: necessary and sufficient under delay** (with no drift). -/
theorem brake_nec_suff (C : Cfg) : Viable C delayE ↔ C.B = true := delay_table C

/-- **No configuration survives a binding budget**, however well designed. -/
theorem resources_bind : ∀ C : Cfg, ¬ Viable C poor := poor_table

end FiveOrgans.CoupledAblation
