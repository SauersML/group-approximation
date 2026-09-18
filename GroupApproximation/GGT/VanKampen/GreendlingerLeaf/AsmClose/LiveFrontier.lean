import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmClose.Statement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Final
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.RoseBelow
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece07Below.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.OuterPinch
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# The region endpoints from the live leaves of the four region chains

Lane gl-assembly-04, second module.  `AsmClose.RegionEndpointsStatement` (`AsmClose/Statement`)
bundles residuals 04, 06, 07 and 10 of the Below waist.  This module proves it from the deepest open
Statement of each region chain on disk, with every hypothesis-free producer already applied:

* residual 04 from `Piece04.ClassPocketWindowShapeStatement`, through
  `Piece04.Final.proof_of_windowShape` (`Piece04/Final`);
* residual 06 from `Piece06.CellRoseUncutLakesBelowStatement`, through `Piece06.proof_of_below_gaps`
  (`Piece06/RoseBelow`), with the bad-corner refinement supplied by the hypothesis-free
  `Piece06.MonogonCorner.badCornerRefinement` (`Piece06/MonogonCorner`);
* residual 07 from `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`, through
  `Piece07Below.proof_of_innerPocketEnclosed` (`Piece07Below/Proof`);
* residual 10 from `P10Rose.RoseRegionMoveSubArcStatement`, through
  `AsmFrontier.outerPinchStep_of_nonRose_subArc` (`AsmFrontier/OuterPinch`), with the non-rose case
  supplied by the hypothesis-free `P10ChordLift.proof` (`P10ChordLift/Proof`).

Endpoints:

* `regionEndpoints_of_liveFrontier`: `RegionEndpointsStatement` from the four live leaves;
* `relativeGreendlingerQuasiGeodesicLeastAreaClosed_of_liveFrontier`: the leaf from them.

Compared with `AsmFrontier.relativeGreendlingerQuasiGeodesicLeastArea_of_tightFrontier`, residual 04
rests on the window shapes instead of the rotation turns, and residual 07 on the enclosed inner
pocket instead of the long inner two-arc.  Each replacement is a proved reduction on disk
(`Piece04.rotationTurns_of_windowShape`, `P07LakeExclusion.innerTwoArcLong_of_innerPocketEnclosed`),
so this frontier is smaller.

This module adds no Statement: the single remaining gap of the lane stays `RegionEndpointsStatement`.
The four binders are the inputs of the region lanes gl-p04-13, gl-p06, gl-p07-15 and gl-p10-08.

## Import hygiene

`GreendlingerLeaf/Assembly`, `Piece04/Proof`, `Piece04/Residual`, `Piece06/Proof`, `Piece07/Proof`
and `Piece10/Proof` are not imported, even transitively.  The residual-10 route uses
`P10Rose/SubArc` (through `AsmFrontier/OuterPinch`).  `P10Rose/Live/Reduction`, which redeclares
`P10Rose.RoseRegionMoveSubArcStatement`, and `Piece10Live`, which redeclares
`Piece10.proof_of_cases`, are both avoided.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmClose

universe u w v

/-- **The four region endpoints from the live leaves of the region chains**: the class-pocket window
shapes (04), the uncut lakes below (06), the enclosed inner pocket (07) and the sub-arc region move
of the rose case (10). -/
theorem regionEndpoints_of_liveFrontier
    (hshape : Piece04.ClassPocketWindowShapeStatement.{u, w, v})
    (hlakes : Piece06.CellRoseUncutLakesBelowStatement.{u, w, v})
    (hinner : P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v})
    (hsub : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    RegionEndpointsStatement.{u, w, v} :=
  ⟨Piece04.Final.proof_of_windowShape hshape,
    Piece06.proof_of_below_gaps hlakes Piece06.MonogonCorner.badCornerRefinement.{u, w, v},
    Piece07Below.proof_of_innerPocketEnclosed hinner,
    AsmFrontier.outerPinchStep_of_nonRose_subArc P10ChordLift.proof.{u, w, v} hsub⟩

/-- **Osin's Lemma 4.4 at least-area diagrams from the live leaves of the four region chains.** -/
theorem relativeGreendlingerQuasiGeodesicLeastAreaClosed_of_liveFrontier
    (hshape : Piece04.ClassPocketWindowShapeStatement.{u, w, v})
    (hlakes : Piece06.CellRoseUncutLakesBelowStatement.{u, w, v})
    (hinner : P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v})
    (hsub : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastAreaClosed_of_regionEndpoints
    (regionEndpoints_of_liveFrontier hshape hlakes hinner hsub)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmClose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmClose.regionEndpoints_of_liveFrontier
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed_of_liveFrontier
