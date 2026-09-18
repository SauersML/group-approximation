import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.Frontier
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece01.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger leaf over the four open frontier Statements

Lane gl-assembly-03, tight variant.  Three of the seven hypotheses of
`relativeGreendlingerQuasiGeodesicLeastArea_of_frontier` (`AsmFrontier/Frontier`) are supplied by
hypothesis-free region endpoints:

* `hbudget` by `Piece01.proof` (`Piece01/Proof`, over the P01 sub-leaf proofs, including
  `P01EmptyTwoGon.proof` in `P01EmptyTwoGon/Endpoint`);
* `hmono` by `Piece06.MonogonCorner.monogonCorner` (`Piece06/MonogonCorner`);
* `hnon` by `P10ChordLift.proof` (`P10ChordLift/Proof`).

What remains are four open region-level Statements:
`Piece04.ClassPocketRotationTurnStatement`, `Piece06.CellRoseUncutLakesBelowStatement`,
`P07LakeExclusion.CellPocketInnerTwoArcLongStatement` and `P10Rose.RoseRegionMoveSubArcStatement`.

This module is kept apart from `AsmFrontier/Frontier` so that the seven-hypothesis endpoint does not
depend on the import trees of the three region endpoints.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams from the four open frontier Statements**: the rotation
turns of a class pocket, the uncut lakes below, the long inner two-arc and the sub-arc region move
of the rose case. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_tightFrontier
    (hrot : Piece04.ClassPocketRotationTurnStatement.{u, w, v})
    (hlakes : Piece06.CellRoseUncutLakesBelowStatement.{u, w, v})
    (hinner : P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{u, w, v})
    (hsub : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_frontier Piece01.proof.{u, w, v} hrot
    Piece06.MonogonCorner.monogonCorner.{u, w, v} hlakes hinner P10ChordLift.proof.{u, w, v} hsub

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.relativeGreendlingerQuasiGeodesicLeastArea_of_tightFrontier
