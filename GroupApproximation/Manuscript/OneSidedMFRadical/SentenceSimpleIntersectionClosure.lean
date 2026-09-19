import GroupApproximation.Manuscript.OneSidedMFRadical.DefectSaturation

/-!
# The simple-intersection route in defect saturation

This file exposes the subgroup internal to census rows 196--198.  The
manuscript's `D ∩ S` is represented as `D.subgroupOf S`, so its normality is
normality in the simple group `S`, not an accidental assertion that `S` is
normal in the ambient group.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

section

variable {G : Type*} [Group G]

/-- **Sentence-census row 196.**  Since the printed defect is normal in `G`,
its intersection with `S`, viewed as a subgroup of `S`, is normal in `S`. -/
theorem manuscriptPrintedDefectIntersectionNormalInSubgroup
    (L S : Subgroup G) :
    ((printedDefect L).subgroupOf S).Normal :=
  (printedDefect_normal L).subgroupOf S

/-- **Sentence-census row 197, first step.**  A nontrivial normal intersection
inside a simple `S` is all of `S`.  The theorem exposes the equality of the
actual intersection subgroup before converting it to `S ≤ D`. -/
theorem manuscriptSimplePrintedDefectIntersectionEqTop
    (L S : Subgroup G) (hS : IsSimpleGroup S)
    (hne : printedDefect L ⊓ S ≠ ⊥) :
    (printedDefect L).subgroupOf S = ⊤ := by
  rcases hS.eq_bot_or_eq_top_of_normal
      ((printedDefect L).subgroupOf S)
      (manuscriptPrintedDefectIntersectionNormalInSubgroup L S) with
    hbot | htop
  · exact absurd
      (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hbot)) hne
  · exact htop

/-- **Sentence-census row 197, second step.**  The top-intersection equality
is exactly the inclusion `S ≤ D`. -/
theorem manuscriptSimpleSubgroupLePrintedDefectViaIntersection
    (L S : Subgroup G) (hS : IsSimpleGroup S)
    (hne : printedDefect L ⊓ S ≠ ⊥) :
    S ≤ printedDefect L :=
  Subgroup.subgroupOf_eq_top.mp
    (manuscriptSimplePrintedDefectIntersectionEqTop L S hS hne)

/-- **Sentence-census row 198, first step.**  Normality of `D` upgrades
`S ≤ D` to containment of the ambient normal closure of `S`. -/
theorem manuscriptNormalClosureSimpleSubgroupLePrintedDefect
    (L S : Subgroup G) (hSD : S ≤ printedDefect L) :
    Subgroup.normalClosure (S : Set G) ≤ printedDefect L :=
  Subgroup.normalClosure_le_normal hSD

/-- **Sentence-census rows 196--198, assembled by the printed route.**  If
`S` normally generates `G`, the preceding normal-intersection calculation
forces the printed defect to be all of `G`. -/
theorem manuscriptPrintedDefectEqTopViaSimpleIntersection
    (L S : Subgroup G) (hS : IsSimpleGroup S)
    (hne : printedDefect L ⊓ S ≠ ⊥)
    (hgen : Subgroup.normalClosure (S : Set G) = ⊤) :
    printedDefect L = ⊤ := by
  apply top_unique
  rw [← hgen]
  exact manuscriptNormalClosureSimpleSubgroupLePrintedDefect L S
    (manuscriptSimpleSubgroupLePrintedDefectViaIntersection L S hS hne)

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
