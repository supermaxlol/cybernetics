import FiveOrgans.CoupledAblation

/-!
# Roles of each capacity: the full classification, and the minimum functional requirements

For an environment `E` and a capacity `o` we define, relative to the exact viable set:

- `Necessary E o`: every viable configuration has `o`.
- `Helpful E o`: in some context, adding `o` turns non-viable into viable.
- `Harmful E o`: in some context, adding `o` turns viable into non-viable.
- `Neutral E o`: switching `o` never changes viability (redundant in `E`).
- `Substitutes E o o'`: in some context either one suffices and removing both fails.
- `Complements E o o'`: in some context both are needed together.
- `MinViable E C`: `C` is viable and removing any present capacity breaks viability. These are the
  **minimum functional requirements**.

Each table in `CoupledAblation` is an exact `↔`. Rewriting with it turns every role into a
decidable statement over the 32 configurations, which is then checked by `decide`.

- `roles_*`: the complete role matrix, every capacity in all seven environments.
- `minimal_*`: the exact list of minimal viable configurations per environment.
- Highlights:
  - `every_role_occurs`: necessary, merely helpful, harmful, neutral, substitutable and
    complementary all occur.
  - `no_capacity_always_necessary`.
  - `no_universal_minimum`: no single capacity set is minimal-viable in every environment.

All statements are *mathematical* necessity inside the coupled model (worst case over admissible
realisations). For the average-case behaviour see `analysis/coupled/`.
-/

namespace FiveOrgans.CoupledRoles
open FiveOrgans.Coupled FiveOrgans.CoupledAblation

inductive Cap | S | M | P | B | W
  deriving DecidableEq

instance : Fintype Cap :=
  ⟨{Cap.S, Cap.M, Cap.P, Cap.B, Cap.W}, fun x => by cases x <;> simp⟩

def Cap.get : Cap → Cfg → Bool
  | .S, C => C.S | .M, C => C.M | .P, C => C.P | .B, C => C.B | .W, C => C.W

def Cap.set : Cap → Bool → Cfg → Cfg
  | .S, v, C => { C with S := v } | .M, v, C => { C with M := v } | .P, v, C => { C with P := v }
  | .B, v, C => { C with B := v } | .W, v, C => { C with W := v }

def cfgEquiv : Cfg ≃ Bool × Bool × Bool × Bool × Bool where
  toFun C := (C.S, C.M, C.P, C.B, C.W)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Cfg := Fintype.ofEquiv _ cfgEquiv.symm

/-! ### Role predicates -/

def Necessary (E : Env) (o : Cap) : Prop := ∀ C, Viable C E → o.get C = true
def Helpful (E : Env) (o : Cap) : Prop := ∃ C, ¬ Viable (o.set false C) E ∧ Viable (o.set true C) E
def Harmful (E : Env) (o : Cap) : Prop := ∃ C, Viable (o.set false C) E ∧ ¬ Viable (o.set true C) E
def Neutral (E : Env) (o : Cap) : Prop := ∀ C, Viable (o.set false C) E ↔ Viable (o.set true C) E
def Substitutes (E : Env) (o o' : Cap) : Prop :=
  ∃ C, Viable (o.set true (o'.set false C)) E ∧ Viable (o.set false (o'.set true C)) E ∧
    ¬ Viable (o.set false (o'.set false C)) E
def Complements (E : Env) (o o' : Cap) : Prop :=
  ∃ C, Viable (o.set true (o'.set true C)) E ∧ ¬ Viable (o.set true (o'.set false C)) E ∧
    ¬ Viable (o.set false (o'.set true C)) E
def MinViable (E : Env) (C : Cfg) : Prop :=
  Viable C E ∧ ∀ o : Cap, o.get C = true → ¬ Viable (o.set false C) E

/-! ### Boolean viability rules (exact, from the tables) -/

def calmB (C : Cfg) : Bool := !C.B || (C.S && C.P)
def delayB (C : Cfg) : Bool := C.B
def shiftFastB (C : Cfg) : Bool := C.B && C.M && C.W && (C.S || C.P)
def shiftSlowB (C : Cfg) : Bool := C.B && C.M && C.W && C.P
def deadbeatB (C : Cfg) : Bool := !C.M && !C.B && (C.S || C.P)
def hostileB (C : Cfg) : Bool := C.S && C.M && C.P && C.B && C.W
def poorB (_ : Cfg) : Bool := false

macro "btab" t:term : tactic => `(tactic| (
  intro C; rw [$t:term C]; rcases C with ⟨s, m, p, b, w⟩
  cases s <;> cases m <;> cases p <;> cases b <;> cases w <;> decide))

theorem calm_b : ∀ C, Viable C calm ↔ calmB C = true := by btab calm_table
theorem delay_b : ∀ C, Viable C delayE ↔ delayB C = true := by btab delay_table
theorem shiftFast_b : ∀ C, Viable C shiftFast ↔ shiftFastB C = true := by btab shiftFast_table
theorem shiftSlow_b : ∀ C, Viable C shiftSlow ↔ shiftSlowB C = true := by btab shiftSlow_table
theorem deadbeat_b : ∀ C, Viable C deadbeatShift ↔ deadbeatB C = true := by
  btab deadbeatShift_table
theorem hostile_b : ∀ C, Viable C hostile ↔ hostileB C = true := by btab hostile_table
theorem poor_b : ∀ C, Viable C poor ↔ poorB C = true := fun C => by
  simp [poorB, poor_table C]

/-- Unfold all role predicates through an exact Boolean rule `f`. -/
macro "roles" hf:term : tactic => `(tactic| (
  simp only [Necessary, Helpful, Harmful, Neutral, Substitutes, Complements, MinViable, $hf:term]
  decide))

/-! ### The complete role matrix -/

theorem roles_calm :
    Helpful calm .S ∧ ¬ Harmful calm .S ∧ Helpful calm .P ∧ ¬ Harmful calm .P ∧
    Neutral calm .M ∧ Neutral calm .W ∧ Harmful calm .B ∧ ¬ Helpful calm .B ∧
    (∀ o, ¬ Necessary calm o) ∧ Complements calm .S .P := by roles calm_b

theorem roles_delay :
    Necessary delayE .B ∧ Helpful delayE .B ∧
    Neutral delayE .S ∧ Neutral delayE .M ∧ Neutral delayE .P ∧ Neutral delayE .W := by
  roles delay_b

theorem roles_shiftFast :
    Necessary shiftFast .M ∧ Necessary shiftFast .B ∧ Necessary shiftFast .W ∧
    ¬ Necessary shiftFast .S ∧ ¬ Necessary shiftFast .P ∧ Helpful shiftFast .S ∧
    Helpful shiftFast .P ∧ (∀ o, ¬ Harmful shiftFast o) ∧ Substitutes shiftFast .S .P ∧
    Complements shiftFast .M .W ∧ Complements shiftFast .B .W := by roles shiftFast_b

theorem roles_shiftSlow :
    Necessary shiftSlow .M ∧ Necessary shiftSlow .P ∧ Necessary shiftSlow .B ∧
    Necessary shiftSlow .W ∧ Neutral shiftSlow .S ∧ ¬ Substitutes shiftSlow .S .P := by
  roles shiftSlow_b

theorem roles_deadbeat :
    Harmful deadbeatShift .M ∧ ¬ Helpful deadbeatShift .M ∧
    Harmful deadbeatShift .B ∧ ¬ Helpful deadbeatShift .B ∧ Neutral deadbeatShift .W ∧
    Helpful deadbeatShift .S ∧ Helpful deadbeatShift .P ∧ Substitutes deadbeatShift .S .P ∧
    (∀ o, ¬ Necessary deadbeatShift o) := by roles deadbeat_b

theorem roles_hostile : ∀ o, Necessary hostile o ∧ Helpful hostile o ∧ ¬ Harmful hostile o := by
  roles hostile_b

theorem roles_poor : ∀ o, Neutral poor o ∧ Necessary poor o := by roles poor_b

/-! ### Minimum functional requirements (exact) -/

def cfg (s m p b w : Bool) : Cfg := ⟨s, m, p, b, w⟩

theorem minimal_calm (C : Cfg) : MinViable calm C ↔ C = cfg false false false false false := by
  revert C; roles calm_b
theorem minimal_delay (C : Cfg) : MinViable delayE C ↔ C = cfg false false false true false := by
  revert C; roles delay_b
theorem minimal_shiftFast (C : Cfg) :
    MinViable shiftFast C ↔ C = cfg true true false true true ∨ C = cfg false true true true true := by
  revert C; roles shiftFast_b
theorem minimal_shiftSlow (C : Cfg) :
    MinViable shiftSlow C ↔ C = cfg false true true true true := by
  revert C; roles shiftSlow_b
theorem minimal_deadbeat (C : Cfg) :
    MinViable deadbeatShift C ↔
      C = cfg true false false false false ∨ C = cfg false false true false false := by
  revert C; roles deadbeat_b
theorem minimal_hostile (C : Cfg) : MinViable hostile C ↔ C = cfg true true true true true := by
  revert C; roles hostile_b
theorem minimal_poor (C : Cfg) : ¬ MinViable poor C := by
  revert C; roles poor_b

/-! ### Highlights -/

/-- No capacity is necessary in every environment that admits a viable configuration. -/
theorem no_capacity_always_necessary : ∀ o : Cap, ¬ Necessary calm o ∨ ¬ Necessary deadbeatShift o :=
  fun o => Or.inl (roles_calm.2.2.2.2.2.2.2.2.1 o)

/-- No single configuration is the minimum requirement in all viable environments: the
requirement set depends on the environment (`calm` needs nothing, `hostile` needs all five). -/
theorem no_universal_minimum : ¬ ∃ C, MinViable calm C ∧ MinViable hostile C := by
  rintro ⟨C, h1, h2⟩
  rw [minimal_calm] at h1
  rw [minimal_hostile, h1] at h2
  simp [cfg] at h2

/-- Every role occurs somewhere: necessary, helpful-but-not-necessary, harmful, neutral,
substitutable and complementary. -/
theorem every_role_occurs :
    Necessary delayE .B ∧ (Helpful shiftFast .S ∧ ¬ Necessary shiftFast .S) ∧
    Harmful deadbeatShift .M ∧ Neutral delayE .W ∧ Substitutes shiftFast .S .P ∧
    Complements shiftFast .M .W :=
  ⟨roles_delay.1, ⟨roles_shiftFast.2.2.2.2.2.1, roles_shiftFast.2.2.2.1⟩, roles_deadbeat.1,
    roles_delay.2.2.2.2.2, roles_shiftFast.2.2.2.2.2.2.2.2.1, roles_shiftFast.2.2.2.2.2.2.2.2.2.1⟩

/-- **Same capacity, opposite roles.** The Brake is necessary in `delayE` and harmful in `calm`;
Memory is necessary in `shiftSlow` and harmful in `deadbeatShift`. -/
theorem role_flip :
    Necessary delayE .B ∧ Harmful calm .B ∧ Necessary shiftSlow .M ∧ Harmful deadbeatShift .M :=
  ⟨roles_delay.1, roles_calm.2.2.2.2.2.2.1, roles_shiftSlow.1, roles_deadbeat.1⟩

end FiveOrgans.CoupledRoles
