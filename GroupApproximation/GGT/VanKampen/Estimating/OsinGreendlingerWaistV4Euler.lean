import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerWaistV4Split
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyOrderEuler
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalkOrder
import GroupApproximation.Meta.AxiomGuard

/-!
# The V4 Greendlinger waist over the Euler order assembly

Osin, arXiv:math/0411039v3, §9, Lemmas 9.4, 9.7 and 4.4.  The waist
`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4` (`OsinGreendlingerWaistV4`) produces
binder 5 on an O-equivalent copy through `osinMultipleEdgePocketRegionCopySection_of_pinchOrder`,
whose residual `CellPocketWalkEitherFollowsStatement` fails at pinch-type touches.  Here binder 5
comes from the Euler order assembly `osinMultipleEdgePocketRegionCopySection_of_pinchOrderEuler`
(`OsinPocketMultipleEdgeCopyOrderEuler`), over `CellPocketWalkEulerStatement`
(`OsinPocketCellSideRelatorCellEuler`), and the exterior is off the side of the walk in some order by
the closed `cellPocketWalkOuterOffSideSomeOrder` (`OsinPocketCellWalkOrder`).

* `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4Euler`: nine named residual Props.
* `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4EulerSplit`: eleven, with the class-word
  cases split through `osinLemma94ClassCases_of_residuals`, as in
  `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4Split`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemmas 9.7 and 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams, V4 over the Euler order assembly**: the waist of
`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4CopySection`, with binder 5 produced by
`osinMultipleEdgePocketRegionCopySection_of_pinchOrderEuler` from the clean copy in both orders, the
closed `cellPocketWalkOuterOffSideSomeOrder`, the Euler equalities of the walk and the cell pinch. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4Euler
    (hloops : OsinLemma94ClassEndLoopsInput.{u, w, v})
    (hpocket : OsinLemma94SameCellPocketInput.{u, w, v})
    (hcases : OsinLemma94ClassCasesInput.{u, w, v})
    (htwogon : OsinTwoGonHoldsSectionStatement.{u, w, v})
    (hcopy : CellPocketCopyCleanBothOrdersStatement.{u, w, v})
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    (hcellPinch : CellPocketPinchPosStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetProperSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4CopySection hloops hpocket hcases htwogon
    (osinMultipleEdgePocketRegionCopySection_of_pinchOrderEuler hcopy
      cellPocketWalkOuterOffSideSomeOrder heuler hcellPinch)
    hfaces hpinch

/-- **Osin's Lemma 4.4 at least-area diagrams, V4 over the Euler order assembly, with the class-word
cases split**: `OsinLemma94ClassCasesInput` from `osinLemma94ClassCases_of_residuals`, over the
closed Case 1 face walk and the closed Case 2. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4EulerSplit
    (hloops : OsinLemma94ClassEndLoopsInput.{u, w, v})
    (hpocket : OsinLemma94SameCellPocketInput.{u, w, v})
    (hrcell : OsinLemma94CaseOneRCellStatement.{u, w, v})
    (hendpoint : OsinLemma94ClassCaseGapEndpointStatement.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (htwogon : OsinTwoGonHoldsSectionStatement.{u, w, v})
    (hcopy : CellPocketCopyCleanBothOrdersStatement.{u, w, v})
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    (hcellPinch : CellPocketPinchPosStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetProperSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4Euler hloops hpocket
    (osinLemma94ClassCases_of_residuals
      (osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk
        (osinLemma94CaseOneSameCell_of_rCell hrcell))
      osinLemma94CaseTwoInput hendpoint hspan)
    htwogon hcopy heuler hcellPinch hfaces hpinch

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4Euler
#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4EulerSplit
