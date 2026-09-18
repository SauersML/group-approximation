import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WalkDegenCaseStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-68: the pinched residual of clause (rest)

The target is `PinchCase.RestStatement` (`PinchCaseRestStatement.lean:24`).  This file states the
residual `pinchRestDone_ResidualStatement`; `PinchRestDoneProof.lean` proves the target from it
(`pinchRestDone_rest_of_residual`).  The math, the case split and the truth check are in the
docstring of `PinchRestDoneProof.lean`.

## The statement

Write `F = witnessFaces a b K C.face`.  A *witness walk* is `ow` with `EnclosedFaceSetSucc X F ow`
and `faceOf (α d) ∈ F` for `d ∈ ow`.  Write (N) for the four noninterleave clauses
(`PinchCase.WalkDegenCaseNoninterleave`), (S) for the four step clauses
(`FourPieceWitness.AbsorbFaceSetStepGood`) and (nd) for "all four contact arcs are nonempty".

The premise block and `¬ case (i)` of `RestStatement`, verbatim, plus one hypothesis:

* **(P)** every witness walk `ow` with (nd) or (N) fails (S), *and* visits a pinched dart:
  some `ow[p]` lies on `G₁` or `G₂` and is not `PocketRun.PinchFreeAt`.

The conclusion is that of `RestStatement`, verbatim.  So the residual only speaks about
configurations where there is no witness walk, or every witness walk either crosses a pinch of
`Π_i`/`Π_j` in a way that breaks a step clause, or has a degenerate contact arc and interleaves.

**LOUD: logical strength.**  As a Prop the residual is *equivalent* to `RestStatement`: the
converse `pinchRestDone_residual_of_rest` just drops (P).  Any residual obtained by adding
hypotheses to `RestStatement` has this property.  It is strictly smaller than `RestStatement`
*and* than the existing `PinchCase.ResidualStatement` in proof content (see the proof file).  It is
not false.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Remaining gap of lane gl-p07-68.**  Clause (rest) of `SoundRoute.PinchCaseStatement`, with
the extra hypothesis (P): every witness walk of `witnessFaces a b K C.face` that has nonempty
contact arcs or satisfies (N) fails the step clauses (S) and visits a pinched dart of `G₁` or
`G₂`.  See the module docstring. -/
def pinchRestDone_ResidualStatement : Prop :=
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
        (∀ outerWalk : List X.toCombMap.Dart,
          EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk →
          (∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
            FourPieceWitness.witnessFaces a b K C.face) →
          ((0 < (a.cellArcList i).length ∧ 0 < (a.cellArcList j).length ∧
              0 < (b.cellArcList i).length ∧ 0 < (b.cellArcList j).length) ∨
            PinchCase.WalkDegenCaseNoninterleave b G₁ G₂ outerWalk) →
          ¬ FourPieceWitness.AbsorbFaceSetStepGood G₁ G₂ outerWalk ∧
            ∃ (p : ℕ) (hp : p < outerWalk.length),
              (outerWalk[p] ∈ G₁.darts ∨ outerWalk[p] ∈ G₂.darts) ∧
              ¬ PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) →
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

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchRestDone_ResidualStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
