import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerOpenResiduals
import GroupApproximation.GGT.VanKampen.Estimating.OsinDescentResidualsPos
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94OneCellSameCell
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarStripStep
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger waist of Lemma 4.4, reduced: closed collar, repaired pinch, one-cell kills

Osin, arXiv:math/0411039v3, §9 and Appendix, Lemmas 9.3, 9.4, 9.7 and 4.4.  An additive reduction
of `relativeGreendlingerQuasiGeodesicLeastArea_of_openResiduals`
(`Estimating/OsinGreendlingerOpenResiduals.lean`, eight binders), through
`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsPos` (`Estimating/OsinDescentResidualsPos.lean`):

* binder 8, `GeodesicCollarStatement`, is discharged by the closed
  `GeodesicCollar.StripStep.geodesicCollarStatement_holds`;
* binder 7 is the repaired pinch `PocketPinchLabelledPosStatement`.  The pinch as stated fails at
  `ε = 0` (`OsinPocketWrapRose.pocketPinchWrapRefutation`), and the section pocket cut reads it only
  at `ε > 0`;
* binder 3, `OsinLemma94CaseOneSameCellStatement`, is reduced to its relator-cell branch
  `OsinLemma94CaseOneRCellStatement` by `osinLemma94CaseOneSameCell_of_rCell`, which refutes the
  value-one branches by the Morse threshold;
* binders 1 and 2 enter as the count piece `OsinLemma94PolygonCountInput`.  Binder 2,
  `OsinLemma94UnboundSameCellStatement`, is false as spelled (a hand model at `ε = 0`, report of lane
  w1-binder-2), so the waist is not stated over it.  The class route
  (`OsinLemma94ClassCountInput`, `OsinLemma94OtherFacingCover.classCovers_of_endLoops_sameCellFactor`,
  `osinLemma94SameCellFactorInput_of_scan`) produces class covers, but nothing on main turns them into
  `OsinLemma94PolygonCountInput` or `OsinLemma94SectionStatement` yet;
* binders 4, 5 and 6 stay as spelled: `OsinTwoGonHoldsSectionStatement`,
  `OsinMultipleEdgePocketRegionSectionStatement` and `OsinSectionPocketFaceSetSectionStatement`.

* `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2`: six named residual Props.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemmas 9.7 and 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams from six residuals**: the Greendlinger waist with
the collar insertion closed, the pinch at a positive side bound, Case 1 across one relator cell from
its relator-cell branch, loops from `osinLoopCutSection`, and the Euler count from C4 and C6′. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2
    (hcount : OsinLemma94PolygonCountInput.{u, w, v})
    (hrcell : OsinLemma94CaseOneRCellStatement.{u, w, v})
    (htwogon : OsinTwoGonHoldsSectionStatement.{u, w, v})
    (hregion : OsinMultipleEdgePocketRegionSectionStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledPosStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsPos
    (osinLemma94Section_of_residuals hcount
      (osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk
        (osinLemma94CaseOneSameCell_of_rCell hrcell)))
    osinLoopCutSection
    (osinPhiPrimeCountSection_of_pieces osinCornerTwoGonSection htwogon)
    hregion hfaces hpinch GeodesicCollar.StripStep.geodesicCollarStatement_holds

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2
