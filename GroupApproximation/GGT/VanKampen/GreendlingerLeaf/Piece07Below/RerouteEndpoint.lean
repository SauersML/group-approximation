import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece07Below.RerouteStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece07Below.RerouteFrontier
import GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.Endpoint
import GroupApproximation.Manuscript.NonMF.Full.GL06h4.PocketAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 07 (below form) from the proved corrected enclosed inner pocket

Lane gl-p07-84.  This module plugs the proved theorem
`GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected` into the reroutes of
`Piece07Below/RerouteStatement` and `Piece07Below/RerouteFrontier`.  After that, the only input
left for residual 07 is the all-cells refutation
`GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement`.  It is true; see the docstring of
`RerouteStatement`.

**LOUD: build caveat.**  This module imports `GL03BPinch/Endpoint`, which in turn imports
`GL03BPinchOrder.ORDERMODULE` and cites `GL03BPinchOrder.lakeWalk_reverse_map_alpha_sublist`.  At
the time of writing, neither exists on disk; `GL03BPinchOrder` holds only `Split` and `Theta`.
`GL03BPinch/Endpoint` is not registered in `GroupApproximation.lean`.  Until that module builds,
this one does not either.  The `_corr` forms in `RerouteStatement` and `RerouteFrontier` take the
corrected statement as an explicit input, and they do not depend on it.

Endpoints:

* `p07Reroute_arcs_allCells`: `CellPocketWalkProperArcsBelowSectionStatement` from `hall`.
  It replaces `Piece07Below.proof_of_innerPocketEnclosed`.
* `p07Reroute_arcs_nearestPocket`: the same target from `GL06h4.NearestCellPocketStatement`,
  through `GL06h4.nearestCellCutSection_of_pocket` and
  `GL06h3.allCellsShortEnclosedRefutedBelowSection_of_nearestCellCutSection`.
* `p07Reroute_regionEndpoints`: `AsmClose.RegionEndpointsStatement`.  It replaces
  `AsmClose.regionEndpoints_of_liveFrontier`.
* `p07Reroute_greendlinger`: `RelativeGreendlingerQuasiGeodesicLeastAreaStatement`.  It replaces
  `AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed_of_liveFrontier`.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 and Lemma 9.7(b)).  It certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

universe u w v

/-- **Piece 07 (below form), rerouted: proper arcs from the all-cells refutation alone** (Osin,
proof of Lemma 9.7(b); `thm:hull`).  The corrected enclosed inner pocket is the proved
`GL03BPinch.innerPocketEnclosedTwoArcCorrected`. -/
theorem p07Reroute_arcs_allCells
    (hall :
      GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} :=
  p07Reroute_arcs_of_corr_allCells
    GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected.{u, w, v} hall

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p07Reroute_arcs_allCells

/-- **Piece 07 (below form), rerouted, from the slit pocket at a nearest cell** (Osin, proof of
Lemma 9.7(b); `thm:hull`).  The all-cells refutation comes from the nearest-cell cut
(`GL06h3`), and the cut from the slit pocket (`GL06h4`). -/
theorem p07Reroute_arcs_nearestPocket
    (h : GroupApproximation.Full.GL06h4.NearestCellPocketStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} :=
  p07Reroute_arcs_allCells
    (Full.GL06h3.allCellsShortEnclosedRefutedBelowSection_of_nearestCellCutSection
      (GroupApproximation.Full.GL06h4.nearestCellCutSection_of_pocket h))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p07Reroute_arcs_nearestPocket

/-- **The four region endpoints, with residual 07 rerouted through the proved corrected enclosed
inner pocket.**  The other three residuals are as in `AsmClose.regionEndpoints_of_liveFrontier`. -/
theorem p07Reroute_regionEndpoints
    (hshape : Piece04.ClassPocketWindowShapeStatement.{u, w, v})
    (hlakes : Piece06.CellRoseUncutLakesBelowStatement.{u, w, v})
    (hall :
      GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v})
    (hsub : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    AsmClose.RegionEndpointsStatement.{u, w, v} :=
  p07Reroute_regionEndpoints_corr hshape hlakes
    GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected.{u, w, v} hall hsub

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p07Reroute_regionEndpoints

/-- **Osin's Lemma 4.4 at least-area diagrams, with residual 07 rerouted** through the proved
corrected enclosed inner pocket.  The inputs are the window shapes (04), the uncut lakes below (06),
the all-cells refutation (07) and the sub-arc region move of the rose case (10). -/
theorem p07Reroute_greendlinger
    (hshape : Piece04.ClassPocketWindowShapeStatement.{u, w, v})
    (hlakes : Piece06.CellRoseUncutLakesBelowStatement.{u, w, v})
    (hall :
      GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v})
    (hsub : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  p07Reroute_greendlinger_corr hshape hlakes
    GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected.{u, w, v} hall hsub

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p07Reroute_greendlinger

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf
