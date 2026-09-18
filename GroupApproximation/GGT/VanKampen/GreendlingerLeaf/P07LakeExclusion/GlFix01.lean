import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFillSucc
import GroupApproximation.Meta.AxiomGuard

/-!
# P07 lake exclusion: the endpoint with the lake-fill gap closed

`Piece07/Proof.lean` cites `P07LakeExclusion.proof : CellPocketWalkProperArcsSectionStatement`,
which is the non-`Below` form.  No such declaration exists.  `P07LakeExclusion/Proof.lean`
only provides `proof_of_gaps`, which takes two gaps and yields the `Below` form.  It cannot
host the endpoint itself: the lake-fill gap is closed in `LakeFillSucc`, and that module
imports `Proof.lean`, so adding the endpoint there would create an import cycle.

This module discharges the first gap with `LakeFill.lakeFillSucc`.  The single remaining
residual is `AllCellsShortLoopStatement`, which is strictly smaller in proof content than
the cited target: the lake-fill case is already closed.  The residual is not on the FALSE
list.  It asks for a short loop enclosing all cells, which is the ball-injectivity and
Greendlinger content.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion

universe u w v

/-- The Piece 07 `Below` section, reduced to the single all-cells short-loop residual. -/
theorem glFix01_proof_of_allCells (h : AllCellsShortLoopStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} :=
  proof_of_gaps LakeFill.lakeFillSucc h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.glFix01_proof_of_allCells

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion
