import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerWaistV4
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassCasesTwoThreshold
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger waist with the two-threshold class cases

Osin, arXiv:math/0411039v3, §9, Lemmas 9.4, 9.7 and 4.4.  An additive waist through
`relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts`:

* Lemma 9.4 along the class route at two thresholds (ruling R2):
  `osinLemma94Section_of_classCountTwoThreshold` (`OsinLemma94ClassSectionTwoThreshold`) over the class
  count from the end loops and the same-cell pocket values, and the class-word cases from
  `osinLemma94ClassCasesTwoThreshold_of_residuals` (`OsinLemma94ClassCasesTwoThreshold`): the side-level
  Case 1 through the closed face walk `osinLemma94CaseOneWalk` and its relator-cell branch
  `OsinLemma94CaseOneRCellStatement`, the closed Case 2 `osinLemma94CaseTwoInput`, and the spanning
  shape `OsinLemma94ClassCaseGapSpanStatement`.  At two thresholds a backwards class pair moves to a
  corner pair (`OsinLemma94ClassPolygons.exists_cornerPair_of_twoThreshold`), so the gap-endpoint shape
  of the one-threshold route leaves the waist.
* Binder 5 whole, `OsinMultipleEdgePocketRegionCopySectionStatement`, as in
  `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4CopySection`.  The cell pinch
  `CellPocketPinchPosStatement` used by the order assemblies is refuted at `.{0, 0, 0}`
  (`OsinPocketCellPinchRose.cellPocketPinchRoseRefutation`), so it is not taken here.
* Binder 6 as the proper face set producer and binder 7 as the section pinch, through
  `osinSectionPocketCutSection_of_residualsSection`.
* Loops from `osinLoopCutSection`; the Euler count from C4 and C6′; the closed collar insertion and
  cell transport.

* `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4TwoThreshold`: eight named residual Props.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemmas 9.7 and 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams, with the two-threshold class cases**: Lemma 9.4 from the
class count and the two-threshold class-word cases (no gap-endpoint shape), binder 5 whole, binder 6 as
the proper face set producer and binder 7 as the section pinch. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4TwoThreshold
    (hloops : OsinLemma94ClassEndLoopsInput.{u, w, v})
    (hpocket : OsinLemma94SameCellPocketInput.{u, w, v})
    (hrcell : OsinLemma94CaseOneRCellStatement.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (htwogon : OsinTwoGonHoldsSectionStatement.{u, w, v})
    (hregion : OsinMultipleEdgePocketRegionCopySectionStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetProperSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts
    (osinLemma94Section_of_classCountTwoThreshold
      (osinLemma94ClassCountInput_of_endLoops hloops
        (osinLemma94SameCellFactorInput_of_scan (osinLemma94SameCellScanInput_of_pocket hpocket)))
      (osinLemma94ClassCasesTwoThreshold_of_residuals
        (osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk
          (osinLemma94CaseOneSameCell_of_rCell hrcell))
        osinLemma94CaseTwoInput hspan))
    (osinMultipleEdgeCutSection_of_copyPieces hregion
      GeodesicCollar.StripStep.geodesicCollarStatement_holds pocketCellTransport)
    osinLoopCutSection
    (osinPhiPrimeCountSection_of_pieces osinCornerTwoGonSection htwogon)
    (osinSectionPocketCutSection_of_residualsSection hfaces hpinch
      GeodesicCollar.StripStep.geodesicCollarStatement_holds)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4TwoThreshold
