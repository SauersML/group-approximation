import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCellSection
import GroupApproximation.GGT.VanKampen.SurgeryRegionPairThickeningRegions
import GroupApproximation.Meta.AxiomGuard

/-!
# Binder 6 with the `regions` stage proved

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  The `regions` stage of the clean copy,
`SectionPocketRegionsCopyStatement`, is proved (`RegionPairThickening.sectionPocketRegionsCopy`).
So the face set between two exterior regions rests on the kept-cell residual alone, and the waist
residual `OsinSectionPocketFaceSetSectionStatement` rests on the Euler equalities of the pocket
walk alone.

* `sectionPocketFaceSetInput_of_keptCell`: `SectionPocketFaceSetInput` from
  `SectionPocketKeptCellStatement`.
* `osinSectionPocketFaceSetSection_of_keptCell`: the waist residual from
  `SectionPocketKeptCellStatement`.
* `osinSectionPocketFaceSetSection_of_euler`: the waist residual from
  `SectionPocketWalkEulerStatement`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **The face set between two exterior regions, from the kept-cell residual alone.** -/
theorem sectionPocketFaceSetInput_of_keptCell
    (hkept : SectionPocketKeptCellStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) :
    SectionPocketFaceSetInput.{u, w, v} D lambda c eps W :=
  sectionPocketFaceSetInput_of_residuals RegionPairThickening.sectionPocketRegionsCopy hkept D
    lambda c eps W

/-- **The waist residual, from the kept-cell residual alone.** -/
theorem osinSectionPocketFaceSetSection_of_keptCell
    (hkept : SectionPocketKeptCellStatement.{u, w, v}) :
    OsinSectionPocketFaceSetSectionStatement.{u, w, v} :=
  osinSectionPocketFaceSetSection_of_residuals RegionPairThickening.sectionPocketRegionsCopy hkept

/-- **Binder 6 from the Euler equalities of the pocket walk alone.** -/
theorem osinSectionPocketFaceSetSection_of_euler
    (heuler : SectionPocketWalkEulerStatement.{u, w, v}) :
    OsinSectionPocketFaceSetSectionStatement.{u, w, v} :=
  osinSectionPocketFaceSetSection_of_regions_euler RegionPairThickening.sectionPocketRegionsCopy
    heuler

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.sectionPocketFaceSetInput_of_keptCell
#audit_axioms GroupApproximation.GGT.VanKampen.osinSectionPocketFaceSetSection_of_keptCell
#audit_axioms GroupApproximation.GGT.VanKampen.osinSectionPocketFaceSetSection_of_euler
