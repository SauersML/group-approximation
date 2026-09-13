import GroupApproximation.GGT.VanKampen.Estimating.OsinDescentResiduals
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SectionResiduals
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerCornerTwoGonSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixGreendlingerParts
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonCount
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOneRun
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CaseOneWalkHolds
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger waist of Lemma 4.4 from its open residuals

Osin, arXiv:math/0411039v3, §9 and Appendix, Lemmas 9.3, 9.4, 9.7 and 4.4.
`relativeGreendlingerQuasiGeodesicLeastArea_of_residuals` (`OsinDescentResiduals`) takes
Lemma 9.4, the loop part, the Euler count of `Φ'_M` and the pocket residuals.  This file passes
the producers on main:
* `osinLemma94Section_of_residuals` (`OsinLemma94SectionResiduals`): Lemma 9.4 from the polygon
  count and Case 1;
* `osinLemma94PolygonCountInput_of_sideBudget` (`OsinLemma94PolygonCount`): the polygon count from
  the side budget and the same-cell statement for unbound darts;
* `osinLemma94CaseOneInput_of_walk` (`OsinUnboundCaseOneRun`) at `osinLemma94CaseOneWalk`
  (`OsinLemma94CaseOneWalkHolds`): Case 1 from its same-cell pairs;
* `osinLoopCutSection` (`OsinAppendixGreendlingerParts`): G2, loops;
* `osinPhiPrimeCountSection_of_pieces` (`OsinAppendixEulerSection`) at C4
  `osinCornerTwoGonSection` (`OsinAppendixEulerCornerTwoGonSection`): the Euler count from C6′.

So the waist depends on eight statements, and on nothing else:
* `OsinLemma94PolygonSideBudgetInput` and `OsinLemma94UnboundSameCellStatement` (the polygon count
  of Lemma 9.4);
* `OsinLemma94CaseOneSameCellStatement` (Case 1 of Lemma 9.4);
* `OsinTwoGonHoldsSectionStatement` (C6′ of Lemma 9.3);
* `OsinMultipleEdgePocketRegionSectionStatement` and `OsinSectionPocketFaceSetSectionStatement`;
* `PocketPinchLabelledStatement`;
* `GeodesicCollarStatement`.

* `relativeGreendlingerQuasiGeodesicLeastArea_of_openResiduals`

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemmas 9.7 and 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams from the open residuals**: the Greendlinger waist,
through `relativeGreendlingerQuasiGeodesicLeastArea_of_residuals`, with Lemma 9.4 from the side
budget and the two same-cell statements, loops from `osinLoopCutSection`, and the Euler count
from C4 and C6′. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_openResiduals
    (hbudget : OsinLemma94PolygonSideBudgetInput.{u, w, v})
    (hsame : OsinLemma94UnboundSameCellStatement.{u, w, v})
    (hsameOne : OsinLemma94CaseOneSameCellStatement.{u, w, v})
    (htwogon : OsinTwoGonHoldsSectionStatement.{u, w, v})
    (hregion : OsinMultipleEdgePocketRegionSectionStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledStatement.{u, w, v})
    (hgeodesic : GeodesicCollarStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
    (osinLemma94Section_of_residuals
      (osinLemma94PolygonCountInput_of_sideBudget hbudget hsame)
      (osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk hsameOne))
    osinLoopCutSection
    (osinPhiPrimeCountSection_of_pieces osinCornerTwoGonSection htwogon)
    hregion hfaces hpinch hgeodesic

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_openResiduals
