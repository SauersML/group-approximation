import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceOffSplit
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClassCells
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-20a: the degenerate off cell of an inside witness

This file proves `PocketFourPieceOffCellStatement` (`FourPieceOffSplit.lean`), part of the
piece-07 residual of Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## Proof

Take a witness `faces ⊆ sideFaces K.walk`.  The walk `K.walk` holds `invDarts K.firstArc`, and
`K.firstArc` is a nonempty arc of `Π_i`.  So `PocketClass.cell_face_not_mem_sideFaces` (lane
gl-p07-03) puts `Π_i` off `sideFaces K.walk`: for `e ∈ K.firstArc`, the walk dart `α e` is a
boundary dart of the side, so `faceOf e = Π_i` is off it.  Then `Π_i ∉ faces`, and `k₀ = i`.

This uses neither the reading nor the emptiness of the arcs.  Those hypotheses are there so that
the statement is exactly the degenerate clause over inside witnesses.

## Endpoint

`pocketFourPieceOff_of_inside : PocketFourPieceInsideStatement → PocketFourPieceOffStatement`, by
`pocketFourPieceOff_of_input_offCell` and `pocketFourPieceOffCell`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- The cell `Π_i` of a pocket walk misses every face set on the side of the walk. -/
theorem fourPieceOffCell_cell_not_mem {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
    {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount} (K : CellPocketWalk D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk) {faces : Finset X.toCombMap.Face}
    (hsub : faces ⊆ sideFaces X.toCombMap K.walk) :
    (cell X i).face ∉ faces := fun hi =>
  PocketClass.cell_face_not_mem_sideFaces hw K.firstArc K.firstArc_pos
    (fun _ hd => PocketClass.mem_walk_of_mem_invDarts_firstArc K hd) (hsub hi)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.fourPieceOffCell_cell_not_mem

/-- **The degenerate off-cell clause over inside witnesses.** -/
theorem pocketFourPieceOffCell : PocketFourPieceOffCellStatement.{u, w, v} := by
  intro _ _ _ _ _ _ _ i _ _ _ K _ _ _ _ _ _ _ _ _ _ hw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hsub
  exact ⟨i, fourPieceOffCell_cell_not_mem K hw hsub⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketFourPieceOffCell

/-- **The four-piece off statement from the inside reading.** -/
theorem pocketFourPieceOff_of_inside (hin : PocketFourPieceInsideStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} :=
  pocketFourPieceOff_of_input_offCell hin pocketFourPieceOffCell

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketFourPieceOff_of_inside

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
