import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerResidualsV2
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellCount
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger waist of Lemma 4.4 along the class route

Osin, arXiv:math/0411039v3, §9 and Appendix, Lemmas 9.3, 9.4, 9.7 and 4.4.  An additive
reduction of `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2`
(`Estimating/OsinGreendlingerResidualsV2.lean`): Lemma 9.4 comes from the class count
(`osinLemma94Section_of_classCount`) rather than from the side-level count piece
`OsinLemma94PolygonCountInput`, whose covering half needs the false
`OsinLemma94UnboundSameCellStatement`.

* The class count is `osinLemma94ClassCountInput_of_endLoops` over the end loops
  `OsinLemma94ClassEndLoopsInput` and hypothesis (ii): `osinLemma94SameCellFactorInput_of_scan`
  over `osinLemma94SameCellScanInput_of_pocket`, whose premise is the pocket value clause
  `OsinLemma94SameCellPocketInput`.  The cutting classes are closed
  (`card_cuttingClasses_le_of_dartMinimal`).
* Case 1 and Case 2 enter on class words, `OsinLemma94ClassCasesInput`.
* Loops, the Euler count from C4, the repaired pinch and the closed collar insertion are as in V2.

* `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV3`: seven named residual Props.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemmas 9.7 and 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams, along the class route**: Lemma 9.4 from the end
loops, the same-cell pocket values and the class-word cases; loops from `osinLoopCutSection`; the
Euler count from C4 and C6′; the pocket residuals with the pinch at a positive side bound; and the
closed collar insertion. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV3
    (hloops : OsinLemma94ClassEndLoopsInput.{u, w, v})
    (hpocket : OsinLemma94SameCellPocketInput.{u, w, v})
    (hcases : OsinLemma94ClassCasesInput.{u, w, v})
    (htwogon : OsinTwoGonHoldsSectionStatement.{u, w, v})
    (hregion : OsinMultipleEdgePocketRegionSectionStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledPosStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsPos
    (osinLemma94Section_of_classCount
      (osinLemma94ClassCountInput_of_endLoops hloops
        (osinLemma94SameCellFactorInput_of_scan (osinLemma94SameCellScanInput_of_pocket hpocket)))
      hcases)
    osinLoopCutSection
    (osinPhiPrimeCountSection_of_pieces osinCornerTwoGonSection htwogon)
    hregion hfaces hpinch GeodesicCollar.StripStep.geodesicCollarStatement_holds

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV3
