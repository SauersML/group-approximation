import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.GapOffFace
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassDisjoint
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shape: discharging the gap-off-face Statement

Lane `gl-p04-10`, bridge.  Lane `gl-p04-11` (module `Piece04.WindowShape.ClassDisjoint`) states
the target of this lane as `ClassDisjoint.GapOffFaceStatement` and reduces class disjointness to
it (`ClassDisjoint.disjoint_of_gapOffFace`).  This module proves that Statement from
`GapOffFace.faceOf_gap_ne`, and so makes class disjointness unconditional.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.GapOffFace

universe u w v

/-- **The lane `gl-p04-10` Statement holds** (closed). -/
theorem gapOffFaceStatement : ClassDisjoint.GapOffFaceStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S P Q k i j hi hj
  exact faceOf_gap_ne Q k i j hi hj

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.GapOffFace.gapOffFaceStatement

/-- **Class darts of distinct cell classes are disjoint** (lane `gl-p04-11`, now unconditional). -/
theorem classDisjointStatement : ClassDisjoint.ClassDisjointStatement.{u, w, v} :=
  ClassDisjoint.disjoint_of_gapOffFace gapOffFaceStatement

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.GapOffFace.classDisjointStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.GapOffFace
