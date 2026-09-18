import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SoundRouteStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-34: the walk-degenerate part of the residual

`PinchCase.ResidualStatement` (`PinchCaseResidualStatement.lean`) splits on whether
`F = witnessFaces a b K C.face` has a witness walk at all.
* No witness walk: this is lane gl-p07-28's `FourPieceWitness.NoPlanarDegenerateStatement`,
  which sibling lane gl-p07-33 reduces to `FourPieceWitness.NoPlanarDegenStepStatement`.
* A witness walk exists: this is `PinchCase.WalkDegenStatement` below.

`WalkDegenStatement` has the premise block, then a witness walk `outerWalk`, then two failure
hypotheses:
* the nondegenerate pinch-free part of case (i) fails: some contact arc is empty, or `G₁` or `G₂`
  has a pinched dart;
* `outerWalk` is not good: the four noninterleaving facts or one of the local step clauses
  S1a/S1b/S2a/S2b fail for it.

Its conclusion is the arc-audit residual conclusion.

**LOUD: strength.**  `WalkDegenStatement` follows from `RestStatement`
(`PinchCase.walkDegen_of_rest`, `PinchCaseProof.lean`), so it is no stronger than (rest).  It is
strictly smaller than (rest): it asserts nothing in the no-walk models (M7, M8) and nothing for
good walks (T2, M2).  The models in which it asserts are M9 (clause 3 fails; branch 1 with
`faces = sideFaces K.walk`) and M11 (S1a fails at `λ_end`; branch 2 with `faces = {C}`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Walk-degenerate residual of lane gl-p07-34.**  A witness walk exists, the nondegenerate
pinch-free part of case (i) fails, and the walk is not good.  Then branch 1 or branch 2 of the
arc-audit residual holds. -/
def WalkDegenStatement : Prop :=
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
      ∀ outerWalk : List X.toCombMap.Dart,
        EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk →
        (∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
          FourPieceWitness.witnessFaces a b K C.face) →
        ¬ (0 < (a.cellArcList i).length ∧ 0 < (a.cellArcList j).length ∧
            0 < (b.cellArcList i).length ∧ 0 < (b.cellArcList j).length ∧
            (∀ d ∈ G₁.darts, PocketRun.PinchFreeAt X.toCombMap d) ∧
            (∀ d ∈ G₂.darts, PocketRun.PinchFreeAt X.toCombMap d)) →
        ¬ (FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts)
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
            ((∃ d ∈ outerWalk, d ∉ G₁.darts) →
              ∀ (p : ℕ) (hp : p < outerWalk.length), outerWalk[p] ∈ G₁.darts →
                outerWalk[(p + 1) % outerWalk.length]'(Nat.mod_lt _
                  (Nat.lt_of_le_of_lt (Nat.zero_le p) hp)) ∈ G₁.darts →
                walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[p]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) ∧
            ((∀ d ∈ outerWalk, d ∈ G₁.darts) →
              ∀ (p q : ℕ) (hp : p < outerWalk.length) (hq : q < outerWalk.length),
                ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[p]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) →
                ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[q]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[q]) → p = q) ∧
            ((∃ d ∈ outerWalk, d ∉ G₂.darts) →
              ∀ (p : ℕ) (hp : p < outerWalk.length), outerWalk[p] ∈ G₂.darts →
                outerWalk[(p + 1) % outerWalk.length]'(Nat.mod_lt _
                  (Nat.lt_of_le_of_lt (Nat.zero_le p) hp)) ∈ G₂.darts →
                walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[p]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) ∧
            ((∀ d ∈ outerWalk, d ∈ G₂.darts) →
              ∀ (p q : ℕ) (hp : p < outerWalk.length) (hq : q < outerWalk.length),
                ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[p]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) →
                ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[q]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[q]) → p = q)) →
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

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.WalkDegenStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase
