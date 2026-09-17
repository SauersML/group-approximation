import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.AssemblyClosed

/-!
# GL03A: the class pocket rotation and turns, unconditionally

Osin (arXiv:math/0411039v3, §9), proof of Lemma 9.7(b), through Lemma 9.4, Case 1 on class words.
This is infrastructure for `thm:hull` (non_mf_groups_exist.tex, around line 2121). It certifies no
printed sentence on its own.

`Piece04.ClassPocketRotationTurnStatement` (module `Piece04.PocketTurns`) is one of the three
frontier binders of `P06Bypass.relativeGreendlingerQuasiGeodesicLeastArea_of_bypassFrontier`.

The proof composes two results already on origin/main:

* `Piece04.rotationTurns_of_windowShape` (module `Piece04.RotationTurns`), which reduces the
  Statement to `Piece04.ClassPocketWindowShapeStatement`;
* `Piece04.WindowShape.Assembly.windowShape` (module `Piece04.WindowShape.AssemblyClosed`), which
  proves that Statement with no hypotheses.
-/

namespace GroupApproximation.Full.GL03A

universe u w v

/-- **The class pocket rotation and turns** (Osin, Lemma 9.4 Case 1; `thm:hull` infrastructure,
non_mf_groups_exist.tex ~2121). For a backwards class pair of one relator cell with no gap
endpoint, `∂Π` rotates to `targetArc ++ B ++ sourceArc ++ A`, and `B ++ X`, `A ++ Y` are
first-turn closed. -/
theorem classPocketRotationTurn :
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.ClassPocketRotationTurnStatement.{u, w, v} :=
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.rotationTurns_of_windowShape
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.Assembly.windowShape

end GroupApproximation.Full.GL03A
