import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SoundRouteStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-34: clause (read) of `SoundRoute.PinchCaseStatement`

`SoundRoute.PinchCaseStatement` (lane gl-p07-31, `SoundRouteStatement.lean`) is a conjunction of
two clauses under one premise block.  This file names the first clause on its own, so that the
two halves can be worked on separately:
* `PinchCase.ReadStatement`: in case (i) (nondegenerate contact arcs and pinch-free `G₁`, `G₂`),
  the four noninterleaving facts for every witness walk.

The second clause is `PinchCase.RestStatement` (`PinchCaseRestStatement.lean`).  The glue
`PinchCase.pinchCase_of_read_rest` is in `PinchCaseGlue.lean`.  The route this lane isolates for
the (rest) clause is described in `PinchCaseResidualStatement.lean`.

The text of the conclusion is copied verbatim from the first conjunct of
`SoundRoute.PinchCaseStatement`, so the two agree definitionally.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Clause (read) of `SoundRoute.PinchCaseStatement`.**  Under its premise block, for
nondegenerate contact arcs, pinch-free `G₁` and `G₂`, and every bridge-free successor outside walk
of `witnessFaces a b K C.face`, the four noninterleaving facts hold. -/
def ReadStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    ∀ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i →
    ∀ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      X.outerFace ∉ sideFaces X.toCombMap K.walk →
      (reclosedMap X.toCombMap (sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (reclosedMap X.toCombMap (sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
        0 < (a.cellArcList i).length → 0 < (a.cellArcList j).length →
          0 < (b.cellArcList i).length → 0 < (b.cellArcList j).length →
          ∀ outerWalk : List X.toCombMap.Dart,
            EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk →
            (∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
              FourPieceWitness.witnessFaces a b K C.face) →
            (∀ d ∈ G₁.darts, PocketRun.PinchFreeAt X.toCombMap d) →
            (∀ d ∈ G₂.darts, PocketRun.PinchFreeAt X.toCombMap d) →
            FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts)
                (invDarts X outerWalk) ∧
              FourPiece.CyclicNoInterleave
                (fun e => e ∉ invDarts X G₁.darts ∧ e ∈ invDarts X G₂.darts)
                (invDarts X outerWalk) ∧
              FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts ∨
                (e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∈ b.sideFrom i))
                (invDarts X outerWalk) ∧
              FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts ∨
                (e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∉ b.sideFrom i))
                (invDarts X outerWalk)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.ReadStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase
