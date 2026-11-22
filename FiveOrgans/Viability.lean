import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Viability and self-undermining adaptation

Part 1 (general). If a policy keeps the viable set `K` invariant, every
trajectory started in `K` stays in `K` forever (`stays_viable`).

Part 2 (counterexample). A two-state world where the myopically best action
destroys viability and loses in the long run:
* state `true` = viable, `false` = collapsed (absorbing, reward 0);
* action `true` = exploit (reward 1, then collapse),
  action `false` = sustain (reward 1/2, stay viable).

Exploit wins every single step (`myopic_prefers_exploit`), yet over any
horizon of 3 or more steps, sustaining earns strictly more
(`sustain_beats_exploit`). This is the formal version of
"winning locally while destroying your future" and the reason viability must
be a constraint, not just another term in a myopic reward.

Status: a constructed example (existence proof of the failure mode), not a
claim about how often it occurs.
-/

namespace FiveOrgans.Viability

section General
variable {X A : Type*}

/-- `π` keeps `K` invariant under dynamics `F`. -/
def Invariant (F : X → A → X) (π : X → A) (K : Set X) : Prop :=
  ∀ x ∈ K, F x (π x) ∈ K

/-- Closed-loop trajectory. -/
def traj (F : X → A → X) (π : X → A) (x₀ : X) : ℕ → X
  | 0 => x₀
  | n + 1 => F (traj F π x₀ n) (π (traj F π x₀ n))

theorem stays_viable {F : X → A → X} {π : X → A} {K : Set X}
    (hI : Invariant F π K) {x₀ : X} (hx : x₀ ∈ K) : ∀ n, traj F π x₀ n ∈ K := by
  intro n
  induction n with
  | zero => exact hx
  | succ n ih => exact hI _ ih

end General

noncomputable section Counterexample

/-- Viable state stays viable only if we do not exploit. -/
def step (s a : Bool) : Bool := s && !a

def reward (s a : Bool) : ℝ := if s then (if a then 1 else 1 / 2) else 0

/-- Total reward over `n` steps under a stationary policy. -/
def total (π : Bool → Bool) : ℕ → Bool → ℝ
  | 0, _ => 0
  | n + 1, s => reward s (π s) + total π n (step s (π s))

def exploit : Bool → Bool := fun _ => true
def sustain : Bool → Bool := fun _ => false

theorem myopic_prefers_exploit : reward true true > reward true false := by
  simp [reward]; norm_num

theorem total_collapsed (π : Bool → Bool) (n : ℕ) : total π n false = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [total, reward, step, ih]

theorem exploit_total (n : ℕ) : total exploit (n + 1) true = 1 := by
  simp [total, reward, step, exploit, total_collapsed]

theorem sustain_total (n : ℕ) : total sustain n true = n / 2 := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    simp [total, reward, step, sustain]
    rw [ih]; ring

theorem exploit_exits : traj step exploit true 1 = false := rfl

theorem sustain_invariant : Invariant step sustain {true} := by
  intro x hx; simp at hx; subst hx; rfl

/-- Over any horizon of at least 3 steps, sustaining strictly beats exploiting. -/
theorem sustain_beats_exploit (n : ℕ) (hn : 3 ≤ n) :
    total exploit n true < total sustain n true := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [exploit_total, sustain_total]
  have : (3 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast hn
  push_cast at this ⊢
  linarith

end Counterexample

end FiveOrgans.Viability
