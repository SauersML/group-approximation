import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces.ContactCharge
import GroupApproximation.Meta.AxiomGuard

/-!
# Holding small faces of the contact map: the endpoint

`proof : OsinLemma94ContactMapHoldingSmallFacesInput`, with `ε₀ = 0`, `K = 4` and `ρ₀ = 1`.

Every holding face is either outer or not.  The held non-outer faces number at most `n + 1`
(`card_inner_le`), and so do the outer faces (`card_outer_le`), where `n` is the relator area of
the diagram of the family.  That area equals `Δ.rCellCount` (`S.equiv.rCellCount_eq`), which is
positive, so `2 (n + 1) ≤ 4 n`.  The nondegeneracy hypothesis is not needed.  The whole argument
is in the docstring of `FaceClassTools`.

## Manuscript status

Infrastructure for `thm:hull` (through the contact count of Osin's Lemma 9.4,
arXiv:math/0411039v3, §9); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces

universe u w v

open scoped Classical

/-- **The nondegenerate small faces holding an object number at most `4 n`.** -/
theorem proof : OsinLemma94ContactMapHoldingSmallFacesInput.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨0, fun _ _ => ⟨4, 1, Nat.one_pos, fun _ _ _ _ Delta _ _ hcells _ S _ _ P _ => ?_⟩⟩
  have hn : S.diagram.rCellCount = Delta.rCellCount := S.equiv.rCellCount_eq
  have hin := card_inner_le P
  have hout := card_outer_le P
  have hsub : (Finset.univ.filter fun F : P.contactMap.Face =>
      P.NondegenerateSmallFace F ∧ P.HoldsObject F) ⊆
      (Finset.univ.filter fun F : P.contactMap.Face => P.HoldsObject F ∧ ¬ IsOuter P F) ∪
      (Finset.univ.filter fun F : P.contactMap.Face => IsOuter P F) := by
    intro F hF
    have hh : P.HoldsObject F := (Finset.mem_filter.mp hF).2.2
    by_cases ho : IsOuter P F
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh, ho⟩)
  have hunion := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces.proof
