import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerWaistV4
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassPairTransfer
import GroupApproximation.Meta.AxiomGuard

/-!
# The V4 Greendlinger waist with the class-word cases split

Osin, arXiv:math/0411039v3, §9, Lemmas 9.4 and 4.4.  The waist
`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4` (`OsinGreendlingerWaistV4`) takes the
class-word cases of Lemma 9.4 whole, as `OsinLemma94ClassCasesInput`.  Here they come from
`osinLemma94ClassCases_of_residuals` (`OsinLemma94ClassPairTransfer`): single-side class-word pairs
are refuted by the side-level Case 1, through the closed face walk `osinLemma94CaseOneWalk` and its
relator-cell branch `OsinLemma94CaseOneRCellStatement`, and by the closed Case 2
`osinLemma94CaseTwoInput`.  The other pairs are the residual shapes
`OsinLemma94ClassCaseGapEndpointStatement` and `OsinLemma94ClassCaseGapSpanStatement`
(`OsinLemma94ClassPairShapes`).

* `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4Split`: twelve named residual Props.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemmas 9.7 and 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams, V4 with the class-word cases split**:
`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4` with `OsinLemma94ClassCasesInput`
produced by `osinLemma94ClassCases_of_residuals` from the relator-cell branch of Case 1 and the two
residual pair shapes, over the closed Case 1 face walk and the closed Case 2. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4Split
    (hloops : OsinLemma94ClassEndLoopsInput.{u, w, v})
    (hpocket : OsinLemma94SameCellPocketInput.{u, w, v})
    (hrcell : OsinLemma94CaseOneRCellStatement.{u, w, v})
    (hendpoint : OsinLemma94ClassCaseGapEndpointStatement.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (htwogon : OsinTwoGonHoldsSectionStatement.{u, w, v})
    (hcopy : CellPocketCopyCleanBothOrdersStatement.{u, w, v})
    (hout : CellPocketWalkOuterOffSideSomeOrderStatement.{u, w, v})
    (hfollow : CellPocketWalkEitherFollowsStatement.{u, w, v})
    (hcellPinch : CellPocketPinchPosStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetProperSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4 hloops hpocket
    (osinLemma94ClassCases_of_residuals
      (osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk
        (osinLemma94CaseOneSameCell_of_rCell hrcell))
      osinLemma94CaseTwoInput hendpoint hspan)
    htwogon hcopy hout hfollow hcellPinch hfaces hpinch

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4Split
