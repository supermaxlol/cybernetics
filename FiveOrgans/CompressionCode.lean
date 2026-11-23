import FiveOrgans.CompressionInfo

/-!
# Predictive compression III: Kraft inequality and the prefix-code entropy bound

`CompressionInfo` bounds the *entropy of the memory states* by `log |M|`. This module states the
coding form. If memory states are written as a binary prefix code, the expected codeword length,
in bits, is at least the entropy of the actions of any safe agent.

- `kraft`: a prefix-free finite set of binary words satisfies `∑ 2^{-|s|} ≤ 1` (by induction on
  the maximum length; split by first bit).
- `kraft_code`: the same for a prefix code `c : M → List Bool`.
- `code_length_ge_entropy`: Kraft lengths `L` satisfy `ent q ≤ log 2 · ∑ q_m L_m` (Gibbs with
  `log x ≤ x − 1`).
- `push_mul_sum`: the expected length under the pushed distribution equals the history average.
- `safe_code_bound`: for a safe agent with a prefix-coded memory, some safe action selector
  `s` has `ent(s) ≤ log 2 · E_w[|c(mem h)|]`. In bits: **expected memory code length ≥ decision
  entropy**.

Scope.
- Prefix codes only. McMillan (Kraft for all uniquely decodable codes) is not formalised.
- Entropy uses natural log, so divide by `log 2` for bits.
-/

namespace FiveOrgans.CompressionCode
open FiveOrgans.Memory FiveOrgans.CompressionInfo Finset Real

variable {H A M : Type*}

/-- No word of `S` is a proper prefix of another. -/
def PrefixFree (S : Finset (List Bool)) : Prop := ∀ s ∈ S, ∀ t ∈ S, s <+: t → s = t

theorem sum_le_one_of_nil {S : Finset (List Bool)} (h : ∀ s ∈ S, s = []) :
    ∑ s ∈ S, ((1 : ℝ) / 2) ^ s.length ≤ 1 := by
  calc ∑ s ∈ S, ((1 : ℝ) / 2) ^ s.length ≤ ∑ s ∈ ({[]} : Finset (List Bool)), ((1 : ℝ) / 2) ^ s.length :=
        sum_le_sum_of_subset_of_nonneg (fun s hs => by simp [h s hs]) (fun _ _ _ => by positivity)
    _ = 1 := by simp

/-- **Kraft inequality** for prefix-free binary words of length `≤ n`. -/
theorem kraft : ∀ (n : ℕ) (S : Finset (List Bool)), (∀ s ∈ S, s.length ≤ n) → PrefixFree S →
    ∑ s ∈ S, ((1 : ℝ) / 2) ^ s.length ≤ 1
  | 0, S, hl, _ => sum_le_one_of_nil fun s hs => List.length_eq_zero_iff.1 (by have := hl s hs; omega)
  | n + 1, S, hl, hp => by
    by_cases h0 : [] ∈ S
    · exact sum_le_one_of_nil fun s hs => (hp _ h0 s hs List.nil_prefix).symm
    have sub : ∀ b : Bool, ∑ t ∈ S.preimage (List.cons b) List.cons_injective.injOn,
        ((1 : ℝ) / 2) ^ t.length ≤ 1 := fun b =>
      kraft n _ (fun t ht => by have := hl _ (mem_preimage.1 ht); simp at this; omega)
        (fun s hs t ht hst => List.cons_injective
          (hp _ (mem_preimage.1 hs) _ (mem_preimage.1 ht) (List.cons_prefix_cons.2 ⟨rfl, hst⟩)))
    have split : ∀ b : Bool, ∑ t ∈ S.preimage (List.cons b) List.cons_injective.injOn,
        ((1 : ℝ) / 2) ^ t.length =
          2 * ∑ s ∈ S, (if s.head? = some b then ((1 : ℝ) / 2) ^ s.length else 0) := by
      intro b
      rw [mul_sum, ← sum_preimage (List.cons b) S List.cons_injective.injOn
        (fun s => 2 * if s.head? = some b then ((1 : ℝ) / 2) ^ s.length else 0) ?_]
      · refine sum_congr rfl fun t _ => ?_
        simp only [List.head?_cons, ↓reduceIte, List.length_cons, pow_succ]
        ring
      · intro s _ hs
        rcases s with _ | ⟨a, t⟩
        · simp
        · have : a ≠ b := fun e => hs ⟨t, by rw [e]⟩
          simp [this]
    have whole : ∑ s ∈ S, ((1 : ℝ) / 2) ^ s.length =
        ∑ s ∈ S, (if s.head? = some false then ((1 : ℝ) / 2) ^ s.length else 0) +
        ∑ s ∈ S, (if s.head? = some true then ((1 : ℝ) / 2) ^ s.length else 0) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun s hs => ?_
      rcases s with _ | ⟨a, t⟩
      · exact absurd hs h0
      · cases a <;> simp
    have h1 := split false
    have h2 := split true
    have s1 := sub false
    have s2 := sub true
    linarith

/-- **Kraft for a prefix code** `c : M → List Bool`. -/
theorem kraft_code [Fintype M] (c : M → List Bool) (hc : ∀ a b, c a <+: c b → a = b) :
    ∑ m, ((1 : ℝ) / 2) ^ (c m).length ≤ 1 := by
  classical
  have hinj : Function.Injective c := fun a b e => hc a b ⟨[], by simp [e]⟩
  rw [← sum_image (f := fun s => ((1 : ℝ) / 2) ^ s.length) (fun a _ b _ e => hinj e)]
  refine kraft ((univ.image c).sup List.length) _ (fun s hs => le_sup (f := List.length) hs) ?_
  rintro s hs t ht hst
  obtain ⟨a, _, rfl⟩ := mem_image.1 hs
  obtain ⟨b, _, rfl⟩ := mem_image.1 ht
  rw [hc a b hst]

/-- **Source-coding lower bound.** Lengths satisfying Kraft cost at least the entropy. -/
theorem code_length_ge_entropy [Fintype M] {q : M → ℝ} (hq : ∀ m, 0 ≤ q m)
    (h1 : ∑ m, q m = 1) {L : M → ℕ} (hK : ∑ m, ((1 : ℝ) / 2) ^ L m ≤ 1) :
    ent q ≤ log 2 * ∑ m, q m * L m := by
  have term : ∀ m, -(q m * log (q m)) - log 2 * (q m * L m) ≤ ((1 : ℝ) / 2) ^ L m - q m := by
    intro m
    rcases (hq m).eq_or_lt with h0 | hp
    · rw [← h0]; simp
    have hx : 0 < ((1 : ℝ) / 2) ^ L m / q m := by positivity
    have hl := log_le_sub_one_of_pos hx
    rw [log_div (by positivity) hp.ne', log_pow, one_div, log_inv] at hl
    have hmul := mul_le_mul_of_nonneg_left hl hp.le
    have : q m * ((1 / 2 : ℝ) ^ L m / q m - 1) = (1 / 2 : ℝ) ^ L m - q m := by field_simp
    rw [one_div] at this
    rw [one_div]
    nlinarith
  have hs := sum_le_sum fun m (_ : m ∈ univ) => term m
  rw [sum_sub_distrib, sum_sub_distrib, h1, ← mul_sum] at hs
  unfold ent
  linarith

theorem push_mul_sum [Fintype H] [Fintype M] [DecidableEq M] (w : H → ℝ) (f : H → M)
    (L : M → ℝ) : ∑ m, push w f m * L m = ∑ h, w h * L (f h) := by
  unfold push
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun h _ => ?_
  simp [ite_mul]

/-- **Expected memory code length ≥ decision entropy.** A safe agent whose memory states are
written in a binary prefix code `c` has a safe action selector `s` with
`ent(s) ≤ log 2 · E_w |c(mem h)|`. -/
theorem safe_code_bound [Fintype H] [Fintype M] [DecidableEq M] [Fintype A] [DecidableEq A]
    {safe : H → A → Prop} {mem : H → M} {π : M → A} (hs : SafeAgent safe mem π)
    {w : H → ℝ} (hw : ∀ h, 0 ≤ w h) (hw1 : ∑ h, w h = 1)
    (c : M → List Bool) (hc : ∀ a b, c a <+: c b → a = b) :
    ∃ s : H → A, (∀ h, safe h (s h)) ∧
      ent (push w s) ≤ log 2 * ∑ h, w h * ((c (mem h)).length : ℝ) := by
  refine ⟨π ∘ mem, hs, (ent_factor_le hw π mem).trans ?_⟩
  rw [← push_mul_sum w mem (fun m => ((c m).length : ℝ))]
  exact code_length_ge_entropy (push_nonneg hw mem) (by rw [push_sum, hw1]) (kraft_code c hc)

end FiveOrgans.CompressionCode
