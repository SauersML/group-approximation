import GroupApproximation.GGT.KazhdanHypGirthEightFromDiagram
import GroupApproximation.GGT.HullSCRelatorFamily
import GroupApproximation.Meta.AxiomGuard

/-!
# The symmetrized triangle relator words

A disc diagram over the positive triangle words `triangleRelatorWords T` cannot
fill a word of negative degree (`KazhdanHypLiteralFillingDegree`).  The standard
convention lets a face read a relator or its formal inverse, and this file names
that family.

* `symTriangleRelatorWords T`: the triangle words together with their formal
  inverses;
* `mem_symTriangleRelatorWords`: a member is a triangle word or the formal
  inverse of one;
* `triangleRelatorWords_subset_sym`;
* `revInv_mem_sym`: the family is closed under formal inversion;
* `listVal_revInv_triangleRelatorWord`: an inverted triangle word spells the
  inverse of the relator value.
-/

namespace GroupApproximation
namespace KazhdanHyp

universe u

variable {Generator TriangleIndex : Type}

/-- The literal triangle words together with their formal inverses. -/
def symTriangleRelatorWords (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    Set (List (GGT.RelLetter (FreeGroup Generator) PEmpty.{u + 1})) :=
  triangleRelatorWords.{u} T ∪ HullSC.RelWord.revInv '' triangleRelatorWords.{u} T

/-- A symmetrized word is a triangle word or the formal inverse of one. -/
theorem mem_symTriangleRelatorWords
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    {v : List (GGT.RelLetter (FreeGroup Generator) PEmpty.{u + 1})} :
    v ∈ symTriangleRelatorWords.{u} T ↔
      (∃ j, triangleRelatorWord.{u} T j = v) ∨
        (∃ j, HullSC.RelWord.revInv (triangleRelatorWord.{u} T j) = v) := by
  constructor
  · rintro (⟨j, rfl⟩ | ⟨w, ⟨j, rfl⟩, rfl⟩)
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr ⟨j, rfl⟩
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr ⟨triangleRelatorWord T j, ⟨j, rfl⟩, rfl⟩

/-- The positive triangle words are symmetrized words. -/
theorem triangleRelatorWords_subset_sym
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    triangleRelatorWords.{u} T ⊆ symTriangleRelatorWords.{u} T :=
  Set.subset_union_left

/-- **The symmetrized family is closed under formal inversion.** -/
theorem revInv_mem_sym {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    {v : List (GGT.RelLetter (FreeGroup Generator) PEmpty.{u + 1})}
    (hv : v ∈ symTriangleRelatorWords.{u} T) :
    HullSC.RelWord.revInv v ∈ symTriangleRelatorWords.{u} T := by
  rcases hv with hv | ⟨w, hw, rfl⟩
  · exact Or.inr ⟨v, hv, rfl⟩
  · rw [HullSC.RelWord.revInv_revInv]
    exact Or.inl hw

/-- **An inverted triangle word spells the inverse relator value.** -/
theorem listVal_revInv_triangleRelatorWord
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (j : TriangleIndex) :
    GGT.RelLetter.listVal (HullSC.RelWord.revInv (triangleRelatorWord.{u} T j)) =
      (GGT.RelLetter.listVal (triangleRelatorWord.{u} T j))⁻¹ :=
  HullSC.RelWord.listVal_revInv _

end KazhdanHyp
end GroupApproximation

#audit_axioms GroupApproximation.KazhdanHyp.mem_symTriangleRelatorWords
#audit_axioms GroupApproximation.KazhdanHyp.triangleRelatorWords_subset_sym
#audit_axioms GroupApproximation.KazhdanHyp.revInv_mem_sym
#audit_axioms GroupApproximation.KazhdanHyp.listVal_revInv_triangleRelatorWord
