import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.Assembly
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.HeadShapeBridge
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplitStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.TailShape
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowTailSplit
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.CellRotationExists
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: `ClassPocketWindowShapeStatement`, unconditionally

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  Endpoint of lane `gl-p04-13`.

Module `WindowShape.Assembly` reduces `Piece04.ClassPocketWindowShapeStatement` (module
`Piece04.RotationTurns`) to three Statements (`windowShape_of_shapes`).  All three upstream lanes
are now on disk, so this module discharges them and closes the Statement.

* `Assembly.HeadShapeStatement` (lane gl-p04-06).  `HeadShape.windowHeadShape_of_split`
  (module `WindowShape.HeadShapeBridge`, which plugs in lanes 01, 02, 03) needs
  `HeadShape.WindowHeadSplitStatement`, proved by `WindowHeadSplit.statement` (lane 04).  The
  result is transported to the Assembly spelling by `Assembly.headShape`.
* `Assembly.TailShapeStatement` (lane gl-p04-07).  `TailShape.windowTailShape_of_windowTailSplit`
  (lanes 01, 02, 03 used directly) needs `TailShape.WindowTailSplitStatement`, proved by
  `Assembly.tailSplit` from `WindowShape.WindowTailSplit.split` (lane 05).  The result is
  transported by `Assembly.tailShape`.
* `Assembly.CellRotationStatement` (lane gl-p04-12): `CellRotation.exists_rotate_assembly`
  (module `WindowShape.CellRotationExists`, through lanes 08, 09, 10, 11).

The transports are eta-expansions: the Statements of the upstream modules have the same text as
the copies in `WindowShape.Assembly`.

## Endpoints

* `Assembly.windowShape : ClassPocketWindowShapeStatement`.
* `Assembly.proof`: the same, under the lane's `proof` spelling.
* `Assembly.rCell : OsinLemma94ClassCaseOneRCellStatement`, through `rCell_of_windowShape`.

Once this module is in the build, lane gl-p04-14 sets
`Final.proof := proof_of_windowShape WindowShape.Assembly.windowShape`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.Assembly

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.CaseOneWalk

/-- **Head shape of a class window arc** (lane gl-p04-06), in the spelling of module
`WindowShape.Assembly`. -/
theorem headShape : HeadShapeStatement.{u, w, v} :=
  fun Q k i j x y arc hi hkind hxy hy hng hne harc =>
    HeadShape.windowHeadShape_of_split WindowHeadSplit.statement Q k i j x y arc hi hkind hxy hy
      hng hne harc

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.Assembly.headShape

/-- **Tail split of a run window** (lane gl-p04-05), in the spelling of
`TailShape.WindowTailSplitStatement`. -/
theorem tailSplit : TailShape.WindowTailSplitStatement.{u, w, v} :=
  fun Q k i x y hi hxy hy hng hne => WindowTailSplit.split Q k i x y hi hxy hy hng hne

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.Assembly.tailSplit

/-- **Tail shape of a class window arc** (lane gl-p04-07), in the spelling of module
`WindowShape.Assembly`. -/
theorem tailShape : TailShapeStatement.{u, w, v} :=
  fun Q k i j x y arc hi hkind hxy hy hng hne harc =>
    TailShape.windowTailShape_of_windowTailSplit tailSplit Q k i j x y arc hi hkind hxy hy hng
      hne harc

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.Assembly.tailShape

/-- **The class pocket window shapes** (endpoint of lane gl-p04-13).  For a backwards class pair of
one relator cell `Π` with no endpoint inside a gap, `∂Π` rotates to `q B p A`, and both run windows
have the head shape and the tail shape against their class window arcs. -/
theorem windowShape : ClassPocketWindowShapeStatement.{u, w, v} :=
  windowShape_of_shapes headShape tailShape CellRotation.exists_rotate_assembly

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.Assembly.windowShape

/-- **The class pocket window shapes**, under the `proof` spelling of lane gl-p04-13. -/
theorem proof : ClassPocketWindowShapeStatement.{u, w, v} :=
  windowShape

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.Assembly.proof

/-- **The relator-cell branch of GapSpan**, unconditionally, through `rCell_of_windowShape`. -/
theorem rCell : OsinLemma94ClassCaseOneRCellStatement.{u, w, v} :=
  rCell_of_windowShape windowShape

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.Assembly.rCell

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.Assembly
