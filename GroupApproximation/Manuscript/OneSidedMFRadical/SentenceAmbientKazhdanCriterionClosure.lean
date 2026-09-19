import GroupApproximation.Manuscript.OneSidedMFRadical.DefectSaturation

/-!
# Applying the compression criterion with the ambient Kazhdan subgroup

This file exposes the exact `K = G` specialization in census row 200.  In
Lean, the ambient group viewed as a subgroup is `⊤ : Subgroup G`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

section

variable {G : Type} [Group G]

/-- Property `(T)` for `G` is property `(T)` for the top subgroup, via the
canonical multiplicative equivalence. -/
theorem manuscriptTopSubgroupHasKazhdanPropertyT
    (hG : HasKazhdanPropertyT.{0, 0} G) :
    HasKazhdanPropertyT.{0, 0} ↥(⊤ : Subgroup G) :=
  HasKazhdanPropertyT.of_mulEquiv Subgroup.topEquiv hG

/-- **Sentence-census row 200.**  The direct full-radical assertion is the
compression criterion with `K = G`: the theorem type displays the top
subgroup's inclusion in the defect, its resulting inclusion in the radical,
and the final equality of the radical with top. -/
theorem manuscriptCompressionCriterionWithAmbientKazhdanSubgroup
    [Countable G] (L : Subgroup G)
    (hL : HasKazhdanPropertyT.{0, 0} ↥L)
    (hG : HasKazhdanPropertyT.{0, 0} G)
    (hD : printedDefect L = ⊤) :
    (⊤ : Subgroup G) ≤ printedDefect L ∧
      (⊤ : Subgroup G) ≤ manuscriptCoronaMFResidual G ∧
      manuscriptCoronaMFResidual G = ⊤ := by
  have htopD : (⊤ : Subgroup G) ≤ printedDefect L := hD.ge
  have htopResidual :
      (⊤ : Subgroup G) ≤ manuscriptCoronaMFResidual G :=
    (manuscriptOneSidedCompressionCriterion G L hL).1 ⊤
      (manuscriptTopSubgroupHasKazhdanPropertyT hG) htopD
  exact ⟨htopD, htopResidual, top_le_iff.mp htopResidual⟩

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
