import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.Statement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.Frontier
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.Tight
import GroupApproximation.Meta.AxiomGuard

/-!
# The pending interface of the unconditional Greendlinger leaf

Lane gl-assembly-12, companion module of the aggregator `GroupApproximation.GreendlingerClosedAll`.

Osin, arXiv:math/0411039v3, Lemma 4.4 at least-area diagrams
(`RelativeGreendlingerQuasiGeodesicLeastAreaStatement`, the Greendlinger waist of Hull's
Theorem 7.1, used for `thm:hull`, tex 1636/2122 of `non_mf_groups_exist.tex`).

The unconditional leaf `AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed` (lane
gl-assembly-04) was not on disk when this lane was authored, and neither were the hypothesis-free
region endpoints of residuals 04, 06, 07 and 10 that it applies.  Of the seven frontier Statements of
`AsmFrontier.relativeGreendlingerQuasiGeodesicLeastArea_of_frontier`, three already have
hypothesis-free producers on disk (`Piece01.proof`, `Piece06.MonogonCorner.monogonCorner`,
`P10ChordLift.proof`, consumed by `AsmFrontier/Tight`).  This module bundles the remaining four as

* `OpenFrontierStatement`: `Piece04.ClassPocketRotationTurnStatement`,
  `Piece06.CellRoseUncutLakesBelowStatement`, `P07LakeExclusion.CellPocketInnerTwoArcLongStatement`
  and `P10Rose.RoseRegionMoveSubArcStatement`;

and proves the two `_of_` reductions

* `openResidualsBelow_of_openFrontier`: the five open residuals of the Below waist
  (`AsmWaist.GreendlingerOpenResidualsBelowStatement`, the input of lane gl-assembly-04);
* `relativeGreendlingerQuasiGeodesicLeastArea_of_openFrontier`: Osin's Lemma 4.4 at least-area
  diagrams, which is the statement of `AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed`.

Lane gl-assembly-04 closes with either the five residual producers or the four producers of
`OpenFrontierStatement`, whichever lands first.

## Truth check

The target is Osin's Lemma 4.4 at least-area diagrams, true.  The four bundled Statements are the
region-level gaps named by the gl-p04/p06/p07/p10 cartographers (true as waist inputs); the bundle
only conjoins them, and the reductions are compositions of proved reductions.

## Manuscript status

Infrastructure for `thm:hull`; certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.ClosedAll

universe u w v

/-- **The four open frontier Statements of the Greendlinger leaf**: the rotation turns of a class
pocket (residual 04), the uncut lakes below (residual 06), the long inner two-arc (residual 07) and
the sub-arc region move of the rose case (residual 10). -/
def OpenFrontierStatement : Prop :=
  Piece04.ClassPocketRotationTurnStatement.{u, w, v} ∧
    Piece06.CellRoseUncutLakesBelowStatement.{u, w, v} ∧
      P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{u, w, v} ∧
        P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}

/-- **The five open residuals of the Below waist from the four open frontier Statements**, with the
budget, the monogon corner and the non-rose step supplied by their hypothesis-free producers. -/
theorem openResidualsBelow_of_openFrontier (h : OpenFrontierStatement.{u, w, v}) :
    AsmWaist.GreendlingerOpenResidualsBelowStatement.{u, w, v} := by
  obtain ⟨hrot, hlakes, hinner, hsub⟩ := h
  exact AsmFrontier.openResidualsBelow_of_frontier Piece01.proof.{u, w, v} hrot
    Piece06.MonogonCorner.monogonCorner.{u, w, v} hlakes hinner P10ChordLift.proof.{u, w, v} hsub

/-- **Osin's Lemma 4.4 at least-area diagrams from the four open frontier Statements.** -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_openFrontier
    (h : OpenFrontierStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} := by
  obtain ⟨hrot, hlakes, hinner, hsub⟩ := h
  exact AsmFrontier.relativeGreendlingerQuasiGeodesicLeastArea_of_tightFrontier hrot hlakes hinner
    hsub

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.ClosedAll

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.ClosedAll.openResidualsBelow_of_openFrontier
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.ClosedAll.relativeGreendlingerQuasiGeodesicLeastArea_of_openFrontier
