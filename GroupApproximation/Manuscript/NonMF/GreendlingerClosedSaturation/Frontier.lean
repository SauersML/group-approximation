import GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation.Carriers
import GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation.PrintedRoute
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.Tight
import GroupApproximation.Meta.AxiomGuard

/-!
# The `lem:saturation` carriers over the four open frontier Statements of the Greendlinger leaf

Lane gl-assembly-06, audit variant.  `Carriers` and `PrintedRoute` state the carriers of tex lines
2136–2170 over the single leaf `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement`.
Lane gl-assembly-03's tight frontier reduction
`GreendlingerLeaf.AsmFrontier.relativeGreendlingerQuasiGeodesicLeastArea_of_tightFrontier`
(`AsmFrontier/Tight`) derives that leaf from four open region-level Statements:

* `Piece04.ClassPocketRotationTurnStatement` (residual 04),
* `Piece06.CellRoseUncutLakesBelowStatement` (residual 06),
* `P07LakeExclusion.CellPocketInnerTwoArcLongStatement` (residual 07),
* `P10Rose.RoseRegionMoveSubArcStatement` (residual 10, rose case).

Composing, the carriers of this lane hold over exactly those four Statements.  This module is kept
apart from `Carriers` and `PrintedRoute` so that they do not depend on the import tree of the region
endpoints (`Piece01/Proof`, `Piece06/MonogonCorner`, `P10ChordLift/Proof`).

## Manuscript status

An interface (Statement-hypothesis) theorem; it certifies no printed sentence on its own.
-/

namespace GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation

/-- **The eight `lem:saturation` / Fournier-Facio carriers over the four open frontier
Statements of the Greendlinger leaf.** -/
theorem saturationCarriers_of_tightFrontier
    (hrot : GGT.VanKampen.GreendlingerLeaf.Piece04.ClassPocketRotationTurnStatement.{0, 0, 0})
    (hlakes : GGT.VanKampen.GreendlingerLeaf.Piece06.CellRoseUncutLakesBelowStatement.{0, 0, 0})
    (hinner :
      GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{0, 0, 0})
    (hsub : GGT.VanKampen.GreendlingerLeaf.P10Rose.RoseRegionMoveSubArcStatement.{0, 0, 0}) :
    SaturationCarriersStatement :=
  saturationCarriers_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.AsmFrontier.relativeGreendlingerQuasiGeodesicLeastArea_of_tightFrontier.{0, 0, 0}
      hrot hlakes hinner hsub)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation.saturationCarriers_of_tightFrontier

/-- **`lem:saturation` along the printed route over the four open frontier Statements of the
Greendlinger leaf.** -/
theorem manuscriptSentence_saturationPrintedRoute_of_tightFrontier
    (hrot : GGT.VanKampen.GreendlingerLeaf.Piece04.ClassPocketRotationTurnStatement.{0, 0, 0})
    (hlakes : GGT.VanKampen.GreendlingerLeaf.Piece06.CellRoseUncutLakesBelowStatement.{0, 0, 0})
    (hinner :
      GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{0, 0, 0})
    (hsub : GGT.VanKampen.GreendlingerLeaf.P10Rose.RoseRegionMoveSubArcStatement.{0, 0, 0}) :
    TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  manuscriptSentence_saturationPrintedRoute_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.AsmFrontier.relativeGreendlingerQuasiGeodesicLeastArea_of_tightFrontier.{0, 0, 0}
      hrot hlakes hinner hsub)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation.manuscriptSentence_saturationPrintedRoute_of_tightFrontier

end GroupApproximation.Manuscript.NonMF.GreendlingerClosedSaturation
