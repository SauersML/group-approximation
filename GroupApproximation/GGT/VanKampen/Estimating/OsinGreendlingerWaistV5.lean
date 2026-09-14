import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerWaistV4
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassCasesTwoThreshold
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyOrderSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellCopyClean
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalkOrder
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchOuterDispatch
import GroupApproximation.Meta.AxiomGuard

/-!
# The live Greendlinger waist

Osin, arXiv:math/0411039v3, §9 and Appendix, Lemmas 9.3, 9.4, 9.7 and 4.4.  An additive waist
through `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts` whose binders avoid every refuted
statement, in particular the positive cell pinch `CellPocketPinchPosStatement`
(`OsinPocketCellPinchRose.cellPocketPinchRoseRefutation`) and the side count needing the false
`OsinLemma94UnboundSameCellStatement`.

* Lemma 9.4 along the class route at two thresholds (ruling R2):
  `osinLemma94Section_of_classCountTwoThreshold` over the class count from the end loops and the
  same-cell pocket values, and `osinLemma94ClassCasesTwoThreshold_of_residuals` over the closed Case 1
  face walk `osinLemma94CaseOneWalk` with its relator-cell branch `OsinLemma94CaseOneRCellStatement`,
  the closed Case 2 `osinLemma94CaseTwoInput`, and the spanning shape
  `OsinLemma94ClassCaseGapSpanStatement`.
* Binder 5 on an O-equivalent copy from the section cell pinch,
  `osinMultipleEdgePocketRegionCopySection_of_pinchSectionOrderEuler`
  (`OsinPocketMultipleEdgeCopyOrderSection`): the clean copy in both orders by the closed
  `cellPocketCopyCleanBothOrders`, the exterior off the side in some order by the closed
  `cellPocketWalkOuterOffSideSomeOrder`, the Euler equalities `CellPocketWalkEulerStatement`, the
  section cell pinch `CellPocketPinchSectionStatement` and the proper arcs of the cell walk
  `CellPocketWalkProperArcsSectionStatement` (model-tested on paper in its module: it fails without
  `OsinCCondition` on one-letter relators, and no counterexample is known under it).  The closed
  collar insertion and `pocketCellTransport` complete the multiple-edge cut.
* Binders 6 and 7 in walk order with proper source and target arcs,
  `OsinSectionPocketFaceSetTwoArcSectionStatement` and `PocketPinchLabelledSectionTwoArcStatement`,
  through `osinSectionPocketCutSection_of_residualsTwoArc` (`OsinPocketPinchOuterDispatch`).
* Loops from `osinLoopCutSection`; the Euler count from C4 (`osinCornerTwoGonSection`) and C6′.

* `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV5`: ten named residual Props.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemmas 9.7 and 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams, over live residuals only**: Lemma 9.4 from the class
count and the two-threshold class-word cases, binder 5 on a copy from the section cell pinch with the
closed clean copy and the closed exterior-off-side order, and binders 6 and 7 in walk order with two
proper arcs, with the closed loops, corner count, collar insertion and cell transport. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV5
    (hloops : OsinLemma94ClassEndLoopsInput.{u, w, v})
    (hpocket : OsinLemma94SameCellPocketInput.{u, w, v})
    (hrcell : OsinLemma94CaseOneRCellStatement.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (htwogon : OsinTwoGonHoldsSectionStatement.{u, w, v})
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    (hcellPinch : CellPocketPinchSectionStatement.{u, w, v})
    (hproper : CellPocketWalkProperArcsSectionStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetTwoArcSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledSectionTwoArcStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts
    (osinLemma94Section_of_classCountTwoThreshold
      (osinLemma94ClassCountInput_of_endLoops hloops
        (osinLemma94SameCellFactorInput_of_scan (osinLemma94SameCellScanInput_of_pocket hpocket)))
      (osinLemma94ClassCasesTwoThreshold_of_residuals
        (osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk
          (osinLemma94CaseOneSameCell_of_rCell hrcell))
        osinLemma94CaseTwoInput hspan))
    (osinMultipleEdgeCutSection_of_copyPieces
      (osinMultipleEdgePocketRegionCopySection_of_pinchSectionOrderEuler cellPocketCopyCleanBothOrders
        cellPocketWalkOuterOffSideSomeOrder heuler hcellPinch hproper)
      GeodesicCollar.StripStep.geodesicCollarStatement_holds pocketCellTransport)
    osinLoopCutSection
    (osinPhiPrimeCountSection_of_pieces osinCornerTwoGonSection htwogon)
    (osinSectionPocketCutSection_of_residualsTwoArc hfaces hpinch
      GeodesicCollar.StripStep.geodesicCollarStatement_holds)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV5
