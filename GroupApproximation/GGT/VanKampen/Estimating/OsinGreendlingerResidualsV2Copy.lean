import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerResidualsV2
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopy
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger waist with the multiple-edge region on a copy

`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2` (`OsinGreendlingerResidualsV2`) takes
binder 5 as `OsinMultipleEdgePocketRegionSectionStatement`, the pocket region on the optimal diagram
itself.  That form is circular: configuration (b′) leaves no pocket region on `S.diagram`, and
excluding it needs Lemma 9.7(b), the lemma being proved.

* `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2CopySection`: the same composition with
  binder 5 on an O-equivalent copy, `OsinMultipleEdgePocketRegionCopySectionStatement`
  (`OsinPocketMultipleEdgeCopy`).
* `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2Copy`: binder 5 replaced by the named
  residuals of the binder-5 route, through `osinMultipleEdgePocketRegionCopySection_of_pinch`, whose
  region data come from `CellPocketFaceSet.copyRegion_of_pinch`: the clean pair on a copy
  (`CellPocketCopyCleanStatement`), the exterior off the side of the cell pocket walk
  (`CellPocketWalkOuterOffSideStatement`), a relator cell on it
  (`CellPocketWalkSideRelatorCellStatement`) and the cell pinch at `0 < ε`
  (`CellPocketPinchPosStatement`).
* `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2_of_copy`: `_of_residualsV2` from the
  copy composition, through `OsinMultipleEdgePocketRegionSectionStatement.copySection`, so the copy
  waist asks for no more.

The other residuals and the closed pieces are those of `_of_residualsV2`: the collar insertion
`GeodesicCollar.StripStep.geodesicCollarStatement_holds`, the cell transport `pocketCellTransport`,
the loop part `osinLoopCutSection` and the corner count `osinCornerTwoGonSection`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemmas 9.7 and 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams from six residuals, with the multiple-edge pocket
region on a copy**: `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2` with binder 5 on an
O-equivalent copy of the least-area diagram. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2CopySection
    (hcount : OsinLemma94PolygonCountInput.{u, w, v})
    (hrcell : OsinLemma94CaseOneRCellStatement.{u, w, v})
    (htwogon : OsinTwoGonHoldsSectionStatement.{u, w, v})
    (hregion : OsinMultipleEdgePocketRegionCopySectionStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledPosStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts
    (osinLemma94Section_of_residuals hcount
      (osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk
        (osinLemma94CaseOneSameCell_of_rCell hrcell)))
    (osinMultipleEdgeCutSection_of_copyPieces hregion
      GeodesicCollar.StripStep.geodesicCollarStatement_holds pocketCellTransport)
    osinLoopCutSection
    (osinPhiPrimeCountSection_of_pieces osinCornerTwoGonSection htwogon)
    (osinSectionPocketCutSection_of_residualsPos hfaces hpinch
      GeodesicCollar.StripStep.geodesicCollarStatement_holds)

/-- **Osin's Lemma 4.4 at least-area diagrams, with binder 5 from the cell pinch**: the waist of
`_of_residualsV2CopySection`, with binder 5 produced by `osinMultipleEdgePocketRegionCopySection_of_pinch`
(through `CellPocketFaceSet.copyRegion_of_pinch`) from four named residuals. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2Copy
    (hcount : OsinLemma94PolygonCountInput.{u, w, v})
    (hrcell : OsinLemma94CaseOneRCellStatement.{u, w, v})
    (htwogon : OsinTwoGonHoldsSectionStatement.{u, w, v})
    (hcopy : CellPocketCopyCleanStatement.{u, w, v})
    (hout : CellPocketWalkOuterOffSideStatement.{u, w, v})
    (hkept : CellPocketWalkSideRelatorCellStatement.{u, w, v})
    (hcellPinch : CellPocketPinchPosStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledPosStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2CopySection hcount hrcell htwogon
    (osinMultipleEdgePocketRegionCopySection_of_pinch hcopy hout hkept hcellPinch) hfaces hpinch

/-- **The copy waist gives the waist on the optimal diagram**: `_of_residualsV2` from
`_of_residualsV2CopySection` through `copySection`. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2_of_copy
    (hcount : OsinLemma94PolygonCountInput.{u, w, v})
    (hrcell : OsinLemma94CaseOneRCellStatement.{u, w, v})
    (htwogon : OsinTwoGonHoldsSectionStatement.{u, w, v})
    (hregion : OsinMultipleEdgePocketRegionSectionStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledPosStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2CopySection hcount hrcell htwogon
    hregion.copySection hfaces hpinch

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2CopySection
#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2Copy
#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2_of_copy
