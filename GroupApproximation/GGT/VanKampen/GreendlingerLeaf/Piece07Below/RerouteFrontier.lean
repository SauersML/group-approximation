import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmClose.Statement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Final
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.RoseBelow
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.OuterPinch
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece07Below.RerouteStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# The AsmClose live frontier, rerouted off the false enclosed inner pocket

Lane gl-p07-84.  `AsmClose.regionEndpoints_of_liveFrontier` (`AsmClose/LiveFrontier`) takes
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement` for residual 07.  That statement is
**FALSE** (see `Piece07Below/RerouteStatement`), so the endpoint is vacuous.  This module rebuilds
the same two endpoints with residual 07 supplied by `p07Reroute_arcs_of_corr_allCells`.  It takes
the corrected statement `hencl` and the all-cells refutation `hall` as inputs.  Residuals 04, 06
and 10 are wired exactly as in `LiveFrontier`.

This module does not import `GL03BPinch/Endpoint`, so it does not depend on that module building.
`Piece07Below/RerouteEndpoint` discharges `hencl` with the proved theorem.  It also does not import
`Piece07Below/Proof`, `AsmClose/LiveFrontier` or any module that proves or assumes the false
statement.

Endpoints:

* `p07Reroute_regionEndpoints_corr`: `AsmClose.RegionEndpointsStatement`.
* `p07Reroute_greendlinger_corr`: `RelativeGreendlingerQuasiGeodesicLeastAreaStatement`.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams).  It certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

universe u w v

/-- **The four region endpoints, with residual 07 rerouted through the corrected enclosed inner
pocket.**  Residual 04 is `Piece04.Final.proof_of_windowShape`.  Residual 06 is
`Piece06.proof_of_below_gaps` with the proved bad-corner refinement.  Residual 07 is
`p07Reroute_arcs_of_corr_allCells`.  Residual 10 is `AsmFrontier.outerPinchStep_of_nonRose_subArc`
with the proved non-rose step. -/
theorem p07Reroute_regionEndpoints_corr
    (hshape : Piece04.ClassPocketWindowShapeStatement.{u, w, v})
    (hlakes : Piece06.CellRoseUncutLakesBelowStatement.{u, w, v})
    (hencl : GroupApproximation.Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v})
    (hall :
      GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v})
    (hsub : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    AsmClose.RegionEndpointsStatement.{u, w, v} :=
  ⟨Piece04.Final.proof_of_windowShape hshape,
    Piece06.proof_of_below_gaps hlakes Piece06.MonogonCorner.badCornerRefinement.{u, w, v},
    p07Reroute_arcs_of_corr_allCells hencl hall,
    AsmFrontier.outerPinchStep_of_nonRose_subArc P10ChordLift.proof.{u, w, v} hsub⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p07Reroute_regionEndpoints_corr

/-- **Osin's Lemma 4.4 at least-area diagrams, with residual 07 rerouted** through the corrected
enclosed inner pocket and the all-cells refutation. -/
theorem p07Reroute_greendlinger_corr
    (hshape : Piece04.ClassPocketWindowShapeStatement.{u, w, v})
    (hlakes : Piece06.CellRoseUncutLakesBelowStatement.{u, w, v})
    (hencl : GroupApproximation.Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v})
    (hall :
      GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v})
    (hsub : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed_of_regionEndpoints
    (p07Reroute_regionEndpoints_corr hshape hlakes hencl hall hsub)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p07Reroute_greendlinger_corr

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf
