import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCSwindleCodeAction
import Mathlib.Data.List.Infix
import GroupApproximation.Meta.AxiomGuard

/-!
# Internal nodes of a finite prefix code

Expanding a leaf adds exactly that leaf to the internal-node set. Old internal
nodes at least as deep as that leaf are incomparable with it, so their shuffles
commute with the new factor. These are the combinatorial inputs to coherence.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The finite set of proper prefixes of the code's leaves. -/
def higSw_internal {d : ℕ} (C : Finset (List (Fin d))) : Finset (List (Fin d)) :=
  C.biUnion fun c => c.inits.toFinset.erase c

theorem higSw_mem_internal {d : ℕ} {C : Finset (List (Fin d))} {u : List (Fin d)} :
    u ∈ higSw_internal C ↔ ∃ c ∈ C, u ≠ c ∧ u <+: c := by
  simp only [higSw_internal, Finset.mem_biUnion, Finset.mem_erase,
    List.mem_toFinset, List.mem_inits]

theorem higSw_leaf_not_internal {d : ℕ} {C : Finset (List (Fin d))}
    (hC : higmanVCTreeNFWitPivot_IsAC C) {c : List (Fin d)} (hc : c ∈ C) :
    c ∉ higSw_internal C := by
  intro hi
  obtain ⟨e, he, hce, hpre⟩ := higSw_mem_internal.mp hi
  exact hC c hc e he hce hpre

/-- Expanding a present leaf adds precisely one internal node. -/
theorem higSw_internal_expand {d : ℕ} (hd : 0 < d)
    {C : Finset (List (Fin d))} {c : List (Fin d)} (hc : c ∈ C) :
    higSw_internal (higmanVCLeafExp_expand C c) = insert c (higSw_internal C) := by
  ext u
  rw [Finset.mem_insert, higSw_mem_internal]
  constructor
  · rintro ⟨e, he, hue, hup⟩
    rcases higmanVCLeafExp_mem_expand.mp he with ⟨_, heC⟩ | ⟨a, rfl⟩
    · exact Or.inr (higSw_mem_internal.mpr ⟨e, heC, hue, hup⟩)
    · have huc : u <+: c := (List.prefix_concat_iff.mp hup).resolve_left hue
      by_cases heq : u = c
      · exact Or.inl heq
      · exact Or.inr (higSw_mem_internal.mpr ⟨c, hc, heq, huc⟩)
  · intro hu
    let a : Fin d := ⟨0, hd⟩
    have hne : c ≠ c ++ [a] := by
      intro heq
      have hl := congrArg List.length heq
      simp only [List.length_append, List.length_singleton] at hl
      omega
    rcases hu with heq | hu
    · subst u
      exact ⟨c ++ [a], higmanVCLeafExp_child_mem C c a, hne, List.prefix_append c [a]⟩
    · obtain ⟨e, he, hue, hup⟩ := higSw_mem_internal.mp hu
      by_cases hec : e = c
      · subst e
        refine ⟨c ++ [a], higmanVCLeafExp_child_mem C c a, ?_,
          hup.trans (List.prefix_append c [a])⟩
        intro heq
        have hl := hup.length_le
        rw [heq, List.length_append, List.length_singleton] at hl
        omega
      · exact ⟨e, higmanVCLeafExp_mem_expand_of_ne he hec, hue, hup⟩

/-- An internal node at least as deep as a leaf is incomparable with that leaf. -/
theorem higSw_internal_deep_incomp {d : ℕ} {C : Finset (List (Fin d))}
    (hC : higmanVCTreeNFWitPivot_IsAC C) {c u : List (Fin d)}
    (hc : c ∈ C) (hu : u ∈ higSw_internal C) (hlen : c.length ≤ u.length) :
    (¬ c <+: u) ∧ (¬ u <+: c) := by
  have huc : u ≠ c := fun e => higSw_leaf_not_internal hC hc (e ▸ hu)
  obtain ⟨e, he, hue, hup⟩ := higSw_mem_internal.mp hu
  constructor
  · intro hcu
    by_cases hce : c = e
    · subst e
      exact hue (hup.eq_of_length (Nat.le_antisymm hup.length_le hcu.length_le))
    · exact hC c hc e he hce (hcu.trans hup)
  · intro hpre
    exact huc (hpre.eq_of_length (Nat.le_antisymm hpre.length_le hlen))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_internal_expand
#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_internal_deep_incomp

end GroupApproximation.BooneHigman.Metabelian.Envelope
