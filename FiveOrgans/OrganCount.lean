import FiveOrgans.OpenWorld

/-!
# Why five, not four: counting organs against demands

`FiveOrganAgent` fixes one hazard stream per organ, so "removing an organ kills" is built in. The
honest form of "why five, not four?" separates **demands** (things the world asks for, each with
a persistent hazard if unmet) from **organs** (mechanisms that meet them), connected by a relation
`serves o j` ("organ `o` meets demand `j`").

* `covered_survives` — every demand served ⇒ survival probability 1 at every horizon.
* `uncovered_dies` — one unserved demand with persistent hazard `h₀ > 0` ⇒ death.
* `viable_covers_all` — **lasting viability forces every demand to be served.**
* `single_purpose_count` — if each organ serves **at most one** demand, serving all `d` demands
  needs at least `d` organs. `fewer_single_purpose_dies` — `m < d` such organs ⇒ death.
* `k_purpose_count` — if each organ serves at most `k` demands, `d ≤ k · m`.
* `generalist_survives` — **one** organ that serves every demand keeps the agent alive.

Reading. "Five organs" is two claims: (i) the world class has five demands with persistent
hazard (EMP?, see `OpenWorld`), and (ii) each mechanism meets only one of them. Given both, five
is the minimum (`five_demands_need_five`). Drop (ii) and the count can fall to one. Whether real
mechanisms are single-purpose is EMP?; the brain and markets have many multi-purpose parts.
-/

namespace FiveOrgans.OrganCount
open Finset FiveOrgans.ViabilityStochastic FiveOrgans.JointViability
open scoped Classical

variable {m d : ℕ}

/-- Demand `j` is met by some organ. -/
def Covered (serves : Fin m → Fin d → Prop) (j : Fin d) : Prop := ∃ o, serves o j

/-- Hazard of demand `k`: `0` if covered, `h₀` if not; no hazard beyond the `d` demands. -/
noncomputable def cov (serves : Fin m → Fin d → Prop) (h₀ : ℝ) (k _i : ℕ) : ℝ :=
  if hk : k < d then (if Covered serves ⟨k, hk⟩ then 0 else h₀) else 0

theorem cov_mem (serves : Fin m → Fin d → Prop) {h₀ : ℝ} (h0 : 0 ≤ h₀) (h1 : h₀ ≤ 1) (k i : ℕ) :
    0 ≤ cov serves h₀ k i ∧ cov serves h₀ k i ≤ 1 := by
  unfold cov; split_ifs <;> exact ⟨by linarith, by linarith⟩

/-- Every demand served ⇒ survival probability `1` at every horizon. -/
theorem covered_survives {serves : Fin m → Fin d → Prop} (hall : ∀ j, Covered serves j)
    (h₀ : ℝ) (n : ℕ) : jointSurv d (cov serves h₀) n = 1 := by
  unfold jointSurv
  refine prod_eq_one fun k hk => ?_
  have hk' := mem_range.1 hk
  have : cov serves h₀ k = fun _ => 0 := funext fun i => by simp [cov, hk', hall]
  rw [this, surv_const]; simp

/-- One unserved demand with persistent hazard kills. -/
theorem uncovered_dies {serves : Fin m → Fin d → Prop} {j : Fin d} (hj : ¬ Covered serves j)
    {h₀ : ℝ} (hpos : 0 < h₀) (h1 : h₀ ≤ 1) {ε : ℝ} (hε : ε < 1) :
    ∃ n, jointSurv d (cov serves h₀) n < 1 - ε :=
  one_out_kills (cov_mem serves hpos.le h1) (k := j.val) j.isLt hpos
    (fun i => by simp [cov, j.isLt, hj]) hε

/-- **Lasting viability forces every demand to be served.** -/
theorem viable_covers_all {serves : Fin m → Fin d → Prop} {h₀ : ℝ} (hpos : 0 < h₀) (h1 : h₀ ≤ 1)
    {c : ℝ} (hc : 0 < c) (hs : ∀ n, c ≤ jointSurv d (cov serves h₀) n) (j : Fin d) :
    Covered serves j := by
  by_contra hj
  obtain ⟨n, hn⟩ := uncovered_dies hj hpos h1 (ε := 1 - c) (by linarith)
  have := hs n
  linarith

/-- **Single-purpose organs: at least one per demand.** -/
theorem single_purpose_count {serves : Fin m → Fin d → Prop}
    (hsp : ∀ o j j', serves o j → serves o j' → j = j') (hall : ∀ j, Covered serves j) :
    d ≤ m := by
  choose g hg using hall
  have hinj : Function.Injective g := fun j j' h => hsp (g j) j j' (hg j) (by rw [h]; exact hg j')
  simpa using Fintype.card_le_of_injective g hinj

/-- **Fewer single-purpose organs than demands ⇒ death.** -/
theorem fewer_single_purpose_dies {serves : Fin m → Fin d → Prop}
    (hsp : ∀ o j j', serves o j → serves o j' → j = j') (hmd : m < d)
    {h₀ : ℝ} (hpos : 0 < h₀) (h1 : h₀ ≤ 1) {ε : ℝ} (hε : ε < 1) :
    ∃ n, jointSurv d (cov serves h₀) n < 1 - ε := by
  have : ∃ j, ¬ Covered serves j := by
    by_contra hcon
    push Not at hcon
    have := single_purpose_count hsp hcon
    omega
  obtain ⟨j, hj⟩ := this
  exact uncovered_dies hj hpos h1 hε

/-- **`k`-purpose organs:** if each organ serves at most `k` demands, covering all `d` needs
`d ≤ k · m`. -/
theorem k_purpose_count {serves : Fin m → Fin d → Prop} {k : ℕ}
    (hk : ∀ o, (univ.filter (fun j => serves o j)).card ≤ k) (hall : ∀ j, Covered serves j) :
    d ≤ k * m := by
  have hsub : (univ : Finset (Fin d)) ⊆ univ.biUnion (fun o => univ.filter (fun j => serves o j)) := by
    intro j _
    obtain ⟨o, ho⟩ := hall j
    exact mem_biUnion.2 ⟨o, mem_univ _, mem_filter.2 ⟨mem_univ _, ho⟩⟩
  calc d = (univ : Finset (Fin d)).card := by simp
    _ ≤ (univ.biUnion (fun o => univ.filter (fun j => serves o j))).card := card_le_card hsub
    _ ≤ ∑ o, (univ.filter (fun j => serves o j)).card := card_biUnion_le
    _ ≤ ∑ _o : Fin m, k := sum_le_sum fun o _ => hk o
    _ = k * m := by simp [mul_comm]

/-- **Five demands, single-purpose organs ⇒ at least five organs** for lasting viability. -/
theorem five_demands_need_five {serves : Fin m → Fin 5 → Prop}
    (hsp : ∀ o j j', serves o j → serves o j' → j = j') {h₀ : ℝ} (hpos : 0 < h₀) (h1 : h₀ ≤ 1)
    {c : ℝ} (hc : 0 < c) (hs : ∀ n, c ≤ jointSurv 5 (cov serves h₀) n) : 5 ≤ m :=
  single_purpose_count hsp (viable_covers_all hpos h1 hc hs)

/-- **A single generalist organ suffices** for any number of demands: the count "five" depends on
the one-organ-one-demand assumption, not on the number of demands alone. -/
theorem generalist_survives (d : ℕ) (h₀ : ℝ) (n : ℕ) :
    jointSurv d (cov (m := 1) (d := d) (fun _ _ => True) h₀) n = 1 :=
  covered_survives (fun _ => ⟨0, trivial⟩) h₀ n

end FiveOrgans.OrganCount
