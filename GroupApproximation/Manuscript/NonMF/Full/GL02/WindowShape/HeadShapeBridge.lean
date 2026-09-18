import GroupApproximation.Manuscript.NonMF.Full.GL02.WindowShape.HeadShape
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassStep
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassSidesSucc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.SideSuccFace
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: the head shape from the head split alone

*GL02 copy.*  Re-proof of the foreign module `Piece04.WindowShape.HeadShapeBridge`
(origin/main blob `9a51d93be`), moved to namespace `Piece04.GL02` since the modules it
imports include files last changed by commits marked WIP.  Only namespaces, the imports of
copied modules, and the qualification of foreign names differ from the original.

The targets of lanes gl-p04-01, 02 and 03 are on disk as `ClassStep.sigma_succ`,
`ClassSidesSucc.succ` and `SideSuccFace.facePerm_last`.  Plugging them into
`HeadShape.windowHeadShape_of_deps` leaves one input, `WindowHeadSplitStatement`, the target of
lane gl-p04-04 (not yet on disk).  `windowHeadShape_of_split` is that reduction.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.HeadShape

universe u w v

/-- Lane gl-p04-01 in the form of `ClassStepStatement`. -/
theorem classStepStatement : ClassStepStatement.{u, w, v} :=
  fun Q k i j hi hj n d e hd he => Piece04.WindowShape.ClassStep.sigma_succ Q k i j hi hj n d e hd he

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.HeadShape.classStepStatement

/-- Lane gl-p04-02 in the form of `ClassSidesSuccStatement`. -/
theorem classSidesSuccStatement : ClassSidesSuccStatement.{u, w, v} :=
  fun Q k i hi => Piece04.WindowShape.ClassSidesSucc.succ Q k i hi

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.HeadShape.classSidesSuccStatement

/-- Lane gl-p04-03 in the form of `SideSuccFaceStatement`. -/
theorem sideSuccFaceStatement : SideSuccFaceStatement.{u, w, v} :=
  fun Q k s hs d t hd ht => Piece04.WindowShape.SideSuccFace.facePerm_last Q k s hs d t hd ht

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.HeadShape.sideSuccFaceStatement

/-- **The head shape of a class window arc from the head split** (lane gl-p04-04). -/
theorem windowHeadShape_of_split (h04 : WindowHeadSplitStatement.{u, w, v}) :
    WindowHeadShapeStatement.{u, w, v} :=
  windowHeadShape_of_deps classStepStatement classSidesSuccStatement sideSuccFaceStatement h04

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.HeadShape.windowHeadShape_of_split

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.HeadShape
