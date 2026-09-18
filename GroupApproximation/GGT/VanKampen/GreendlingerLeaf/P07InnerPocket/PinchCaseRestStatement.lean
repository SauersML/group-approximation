import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SoundRouteStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-34: clause (rest) of `SoundRoute.PinchCaseStatement`

`PinchCase.RestStatement` is the second conjunct of `SoundRoute.PinchCaseStatement` (lane
gl-p07-31), stated on its own: under the premise block of the arc-audit residual, if case (i)
fails (some contact arc is empty, or `G₁` or `G₂` has a pinched dart, or `witnessFaces a b K C.face`
has no bridge-free successor outside walk), then the arc-audit residual's conclusion holds.

The text is copied verbatim from `SoundRouteStatement.lean`, so the two agree definitionally.
The route this lane isolates for it is in `PinchCaseResidualStatement.lean`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Clause (rest) of `SoundRoute.PinchCaseStatement`**: the arc-audit residual outside case (i),
i.e. in the degenerate-arc, pinched and no-walk cases. -/
def RestStatement : Prop :=
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
        ¬ (0 < (a.cellArcList i).length ∧ 0 < (a.cellArcList j).length ∧
            0 < (b.cellArcList i).length ∧ 0 < (b.cellArcList j).length ∧
            (∀ d ∈ G₁.darts, PocketRun.PinchFreeAt X.toCombMap d) ∧
            (∀ d ∈ G₂.darts, PocketRun.PinchFreeAt X.toCombMap d) ∧
            ∃ outerWalk : List X.toCombMap.Dart,
              EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk ∧
                ∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
                  FourPieceWitness.witnessFaces a b K C.face) →
          (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
            EnclosedFaceSetSucc X faces outerWalk ∧ C.face ∈ faces ∧
              faces ⊆ sideFaces X.toCombMap K.walk ∧
              (∀ d ∈ outerWalk,
                X.toCombMap.alpha d ∈ invDarts X G₁.darts ∨
                X.toCombMap.alpha d ∈ invDarts X G₂.darts ∨
                (X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ sideFaces X.toCombMap K.walk ∧
                  X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ a.1 ∧
                  X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ b.1 ∧
                  (walkKeep X.toCombMap K.walk (X.toCombMap.alpha d) ∨
                    walkKeep X.toCombMap a.2.boundary.cycle (X.toCombMap.alpha d) ∨
                    walkKeep X.toCombMap b.2.boundary.cycle (X.toCombMap.alpha d)))) ∧
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
                (invDarts X outerWalk) ∧
              (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
                (invDarts X outerWalk).rotate m = U ++ V →
                (∀ e ∈ U, e ∈ invDarts X G₁.darts) →
                (∃ e ∈ V, e ∉ invDarts X G₁.darts) →
                ∃ A : CyclicArc (cellDarts X i), U = invDarts X A.darts) ∧
              ((∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₁.darts) →
                ∃ (n : ℕ) (A : CyclicArc (cellDarts X i)),
                  invDarts X (outerWalk.rotate n) = invDarts X A.darts) ∧
              (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
                (invDarts X outerWalk).rotate m = U ++ V →
                (∀ e ∈ U, e ∈ invDarts X G₂.darts) →
                (∃ e ∈ V, e ∉ invDarts X G₂.darts) →
                ∃ A : CyclicArc (cellDarts X j), U = invDarts X A.darts) ∧
              ((∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₂.darts) →
                ∃ (n : ℕ) (A : CyclicArc (cellDarts X j)),
                  invDarts X (outerWalk.rotate n) = invDarts X A.darts)) ∨
          (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart) (n : ℕ),
            EnclosedFaceSetSucc X faces outerWalk ∧ C.face ∈ faces ∧
              ((∃ A : CyclicArc (cellDarts X i),
                  invDarts X (outerWalk.rotate n) = invDarts X A.darts) ∨
                (∃ A : CyclicArc (cellDarts X j),
                  invDarts X (outerWalk.rotate n) = invDarts X A.darts)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.RestStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase
