import GroupApproximation.Manuscript.NonMF.Full.GL03C.JunctionReduction
import GroupApproximation.Manuscript.NonMF.Full.GL03C.FilterWalk

/-!
# The rose endpoints

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  This is infrastructure for `thm:hull` in
`non_mf_groups_exist.tex` (around line 2121).

From `roseFilterWalk : RoseFilterWalkStatement` (module `Full/GL03C/FilterWalk`):

* `roseExtremalJunction : P10RoseExtremalTrim.RoseExtremalJunctionStatement`;
* `roseRegionMoveSubArc : P10Rose.RoseRegionMoveSubArcStatement` (the endpoint needed by GL06);
* `rose : P10ChordLift.RoseStepStatement`;
* `piece10 : PocketOuterPinchStepSectionStatement`.

This module is kept at its final path.  It lands with `Full/GL03C/FilterWalk`, after the live rose
chain (`P10Rose/Live/*`, whose last commit message contains "WIP") is cleared.
-/

namespace GroupApproximation.Full.GL03C

universe u w v

open GroupApproximation.GGT.VanKampen

/-- **The rose planarity core** (Osin 9.7(b), `thm:hull` infrastructure). -/
theorem roseExtremalJunction :
    GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement.{u, w, v} :=
  roseExtremalJunction_of_filterWalk roseFilterWalk

/-- **The sub-arc region move of the rose step** (Osin 9.7(b), `thm:hull` infrastructure). -/
theorem roseRegionMoveSubArc : GreendlingerLeaf.P10Rose.RoseRegionMoveSubArcStatement.{u, w, v} :=
  GreendlingerLeaf.P10Rose.regionMoveSubArc_of_singleRegionMove
    (GreendlingerLeaf.P10RoseExtremalTrim.singleRegionMove_of_junction roseExtremalJunction)

/-- **The rose step** (Osin 9.7(b), `thm:hull` infrastructure). -/
theorem rose : GreendlingerLeaf.P10ChordLift.RoseStepStatement.{u, w, v} :=
  GreendlingerLeaf.P10RoseExtremalTrim.rose_of_junction roseExtremalJunction

/-- **The outer-pinch step of the section pinch** (Osin 9.7(b), `thm:hull` infrastructure). -/
theorem piece10 : PocketOuterPinchStepSectionStatement.{u, w, v} :=
  GreendlingerLeaf.Piece10.proof_of_extremalJunction roseExtremalJunction

end GroupApproximation.Full.GL03C
