import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionOfSimple
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCollarOfGeodesic
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueOuterTransport
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueCellTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# The section pocket cut from its residual pieces

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of
`Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

`sectionPocketCutInput_of_pieces` (`OsinPocketPieces`) takes five pieces besides the face set
producer.  Four of them are proved:
* `pocketRegionOfSimple` (`OsinPocketRegionOfSimple`): a simple pocket face set is a carrier;
* `pocketCollarStatement_of_geodesicCollar` (`OsinPocketCollarOfGeodesic`): the collar of a
  nondegenerate carrier from the collar insertion `GeodesicCollarStatement`;
* `pocketCellTransport` (`OsinPocketGlueCellTransport`, lane `go-lemma42`): the regions of the
  glued copy to a cell outside the pocket;
* `pocketOuterTransport` (`OsinPocketGlueOuterTransport`, lane `hull-select`): the regions of the
  glued copy to the boundary arc of the pocket.

This file passes them.  So the section pocket cut depends on the face set producer
(`OsinSectionPocketFaceSetSectionStatement`, lane `kh-ejz`), the pinch
(`PocketPinchLabelledStatement`, lane `hull-respell`) and the collar insertion
(`GeodesicCollarStatement`, lane `kh-torsion`), and on nothing else.

* `sectionPocketCutInput_of_residuals`
* `osinSectionPocketCutSection_of_residuals`

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **`SectionPocketCutInput` from the residual pieces**: the pinch and the collar insertion, given
the face set between the two regions. -/
theorem sectionPocketCutInput_of_residuals
    (hpinch : PocketPinchLabelledStatement.{u, w, v})
    (hgeodesic : GeodesicCollarStatement.{u, w, v})
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : lambda ≤ 1) (hc : 0 ≤ c)
    (hfaces : SectionPocketFaceSetInput.{u, w, v} D lambda c eps W) :
    SectionPocketCutInput.{u, w, v} D lambda c eps W :=
  sectionPocketCutInput_of_pieces hpinch pocketRegionOfSimple
    (pocketCollarStatement_of_geodesicCollar hgeodesic) pocketCellTransport pocketOuterTransport
    hcondition hlambda hc hfaces

/-- **The section pocket producer from the residual pieces, uniformly in the parameters**: the
face set producer, the pinch and the collar insertion. -/
theorem osinSectionPocketCutSection_of_residuals
    (hfaces : OsinSectionPocketFaceSetSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledStatement.{u, w, v})
    (hgeodesic : GeodesicCollarStatement.{u, w, v}) :
    OsinSectionPocketCutSectionStatement.{u, w, v} :=
  osinSectionPocketCutSection_of_pieces hfaces hpinch pocketRegionOfSimple
    (pocketCollarStatement_of_geodesicCollar hgeodesic) pocketCellTransport pocketOuterTransport

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.sectionPocketCutInput_of_residuals
#audit_axioms GroupApproximation.GGT.VanKampen.osinSectionPocketCutSection_of_residuals
