import GroupApproximation.Manuscript.NonMF.Full.GL02.WindowShape.CellRotation
import GroupApproximation.Manuscript.NonMF.Full.GL02.WindowShape.GapOffFaceBridge
import GroupApproximation.Manuscript.NonMF.Full.GL02.WindowShape.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shape: the rotation of the cell to `q B p A`, unconditionally

*GL02 copy.*  Re-proof of the foreign module `Piece04.WindowShape.CellRotationExists`
(origin/main blob `8b3beb361`), moved to namespace `Piece04.GL02` since the modules it
imports include files last changed by commits marked WIP.  Only namespaces, the imports of
copied modules, and the qualification of foreign names differ from the original.

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  This is the endpoint of lane
`gl-p04-12`.

Module `WindowShape.CellRotation` proves the rotation `∂Π.rotate n = q B p A` from
`CellRotation.ClassDisjointStatement` (`exists_rotate_of_classDisjoint`).  Lane `gl-p04-11` is now
on disk: `GapOffFace.classDisjointStatement` (module `WindowShape.GapOffFaceBridge`) proves
`ClassDisjoint.ClassDisjointStatement` without hypotheses.  The two Statements have the same text,
so this module transports the proof and closes the rotation.

## Endpoints

* `CellRotation.classDisjoint : CellRotation.ClassDisjointStatement`.
* `CellRotation.exists_rotate : CellRotation.CellRotationStatement` (lane `gl-p04-12` target).
* `CellRotation.exists_rotate_assembly : Assembly.CellRotationStatement`: the same rotation for the
  copy of the Statement in module `WindowShape.Assembly` (lane `gl-p04-13`), so that the assembly
  can write `windowShape_of_shapes HeadShape… TailShape… CellRotation.exists_rotate_assembly`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.CellRotation

universe u w v

/-- **Class darts of distinct cell classes are disjoint** (lane `gl-p04-11`), in the spelling of
module `WindowShape.CellRotation`. -/
theorem classDisjoint :
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.CellRotation.ClassDisjointStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S P Q k i i' j hi hi' hii' hk hk'
  exact GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.GapOffFace.classDisjointStatement
    Q k i i' j hi hi' hii' hk hk'

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.CellRotation.classDisjoint

/-- **The rotation of the cell to `q B p A`** (endpoint of lane `gl-p04-12`).  Under the hypotheses
of `ClassPocketWindowShapeStatement`, `∂Π` rotates to the target arc, a complement, the source arc
and a complement. -/
theorem exists_rotate :
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.CellRotation.CellRotationStatement.{u, w, v} :=
  exists_rotate_of_classDisjoint classDisjoint

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.CellRotation.exists_rotate

/-- **The rotation of the cell to `q B p A`**, for the copy of the Statement in module
`WindowShape.Assembly` (lane `gl-p04-13`). -/
theorem exists_rotate_assembly :
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.Assembly.CellRotationStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S P Q k C hback hnogap j sourceArc targetArc X Y r
    hks hkt htrav hsource htarget
  exact exists_rotate Q k C hback hnogap j sourceArc targetArc X Y r hks hkt htrav hsource
    htarget

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.CellRotation.exists_rotate_assembly

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.CellRotation
