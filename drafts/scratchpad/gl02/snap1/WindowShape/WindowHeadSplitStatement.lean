import GroupApproximation.Manuscript.NonMF.Full.GL02.WindowShape.HeadShapeDeps
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: the head split discharges its interface

*GL02 copy.*  Re-proof of the foreign module `Piece04.WindowShape.WindowHeadSplitStatement`
(origin/main blob `63a4ed3fa`), moved to namespace `Piece04.GL02` since the modules it
imports include files last changed by commits marked WIP.  Only namespaces, the imports of
copied modules, and the qualification of foreign names differ from the original.

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  Lane `gl-p04-04`, interface.

`WindowHeadSplit.statement` proves `HeadShape.WindowHeadSplitStatement`, the input left open by
`HeadShape.windowHeadShape_of_deps` and `HeadShapeBridge`.  The proof is
`WindowHeadSplit.split` with every argument passed through.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.WindowHeadSplit

universe u w v

/-- **The head split interface** (lane gl-p04-04): `HeadShape.WindowHeadSplitStatement` holds. -/
theorem statement : HeadShape.WindowHeadSplitStatement.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ Q k i x y hi hxy hy hng hne
  exact Piece04.WindowShape.WindowHeadSplit.split Q k i x y hi hxy hy hng hne

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.WindowHeadSplit.statement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.WindowHeadSplit
