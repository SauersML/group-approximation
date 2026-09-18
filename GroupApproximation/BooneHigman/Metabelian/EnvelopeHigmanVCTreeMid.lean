import Mathlib.Data.List.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# A word of intermediate length, incomparable with two given words (lane bh-met-77i)

Pure word combinatorics used by the defect reduction (`EnvelopeHigmanVCTreeDefect`).

Let `u = p a` be a nonempty word and `v` a word with `|v| ≥ |u| + 1`, over an alphabet with two
distinct letters `x₀ ≠ x₁`.  Then `w = p b c` has length `|u| + 1` and is incomparable (neither
is a prefix of the other) with both `u` and `v` (`higmanVCTree_exists_mid`), where

* `b ≠ a`, so `w` and `u` differ at position `|p|`;
* `c` is not the letter of `v` at position `|p| + 1`, so `w` is not a prefix of `v`; since
  `|v| ≥ |w|`, `v` is not a prefix of `w` either.

`scratchpad/bh-met-77i/check.py` confirms the construction by brute force (`d = 2, 3`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The letter of `p ++ q` at position `|p|` is the first letter of `q`. -/
theorem higmanVCTree_getElem?_len {X : Type*} (p q : List X) :
    (p ++ q)[p.length]? = q[0]? := by
  rw [List.getElem?_append_right (Nat.le_refl p.length), Nat.sub_self]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTree_getElem?_len

/-- The letter of `p ++ [b, c] ++ t` at position `|p| + 1` is `c`. -/
theorem higmanVCTree_getElem?_succ {X : Type*} (p t : List X) (b c : X) :
    (p ++ [b, c] ++ t)[p.length + 1]? = some c := by
  rw [List.append_assoc, List.getElem?_append_right (by omega : p.length ≤ p.length + 1)]
  simp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTree_getElem?_succ

/-- Some letter differs from a given one. -/
theorem higmanVCTree_exists_ne {X : Type*} {x₀ x₁ : X} (hx : x₀ ≠ x₁) (a : X) :
    ∃ b : X, b ≠ a := by
  by_cases h : a = x₀
  · refine ⟨x₁, ?_⟩
    rw [h]
    exact hx.symm
  · exact ⟨x₀, fun e => h e.symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTree_exists_ne

/-- Some letter is not the letter of `v` at position `i`. -/
theorem higmanVCTree_exists_ne_get {X : Type*} {x₀ x₁ : X} (hx : x₀ ≠ x₁) (v : List X)
    (i : ℕ) : ∃ c : X, v[i]? ≠ some c := by
  by_cases h : v[i]? = some x₀
  · refine ⟨x₁, ?_⟩
    rw [h]
    exact fun e => hx (Option.some.inj e)
  · exact ⟨x₀, h⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTree_exists_ne_get

/-- **Intermediate word.**  For `u = p ++ [a]` and `|v| ≥ |u| + 1`, some word `w` of length
`|u| + 1` is incomparable with both `u` and `v`. -/
theorem higmanVCTree_exists_mid {X : Type*} {x₀ x₁ : X} (hx : x₀ ≠ x₁) (p : List X) (a : X)
    {v : List X} (hv : p.length + 2 ≤ v.length) :
    ∃ w : List X, w.length = p.length + 2 ∧ ¬ (p ++ [a]) <+: w ∧ ¬ w <+: (p ++ [a]) ∧
      ¬ w <+: v ∧ ¬ v <+: w := by
  obtain ⟨b, hb⟩ := higmanVCTree_exists_ne hx a
  obtain ⟨c, hc⟩ := higmanVCTree_exists_ne_get hx v (p.length + 1)
  have hlw : (p ++ [b, c]).length = p.length + 2 := by simp
  have hla : (p ++ [a]).length = p.length + 1 := by simp
  have hwv : ¬ (p ++ [b, c]) <+: v := by
    rintro ⟨t, ht⟩
    have e : v[p.length + 1]? = some c := by
      rw [← ht]
      exact higmanVCTree_getElem?_succ p t b c
    exact hc e
  refine ⟨p ++ [b, c], hlw, ?_, ?_, hwv, ?_⟩
  · rintro ⟨t, ht⟩
    have e : (p ++ [a] ++ t)[p.length]? = (p ++ [b, c])[p.length]? := by rw [ht]
    rw [List.append_assoc, higmanVCTree_getElem?_len, higmanVCTree_getElem?_len,
      List.singleton_append, List.getElem?_cons_zero, List.getElem?_cons_zero] at e
    exact hb (Option.some.inj e).symm
  · intro h
    have hl := h.length_le
    omega
  · intro h
    have hl := h.length_le
    have e : v = p ++ [b, c] := h.eq_of_length (by omega)
    exact hwv ⟨[], by rw [List.append_nil]; exact e.symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTree_exists_mid

end GroupApproximation.BooneHigman.Metabelian.Envelope
