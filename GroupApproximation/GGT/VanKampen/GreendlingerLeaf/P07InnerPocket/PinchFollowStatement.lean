import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchFollowTurn
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchRestDoneProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-69: a new face set only needs its outer turns

The target is `pinchRestDone_ResidualStatement` (`PinchRestDoneStatement.lean:45`).  In its hard
configurations (M9: an empty contact arc, M11: branch 2) the conclusion needs a new face set with
its own `EnclosedFaceSetSucc` walk.  The only constructor is `enclosedFaceSetSuccOfNoncrossing`,
which needs `FollowsBoundary`.

`pinchFollow_ResidualStatement` keeps the premise block of the target verbatim, (P) included.  Its
conclusion adds a second way out: give a noncrossing closed walk `w'` with the exterior face off
its side and the *local* outer turn condition `pinchFollow_OuterTurn`, and prove the target's
conclusion *assuming* `EnclosedFaceSetSucc X (sideFaces X w') (invDarts X w')`.  That face set is
then built by `pinchFollow_enclosed_of_turn` (`PinchFollowTurn.lean`), and
`pinchFollow_residual_of_statement` is the `_of_` reduction.

**LOUD: logical strength.**  As a Prop the statement is *equivalent* to the target (see
`pinchFollow_statement_of_residual`): the new disjunct implies the old one by the proved lemma.
It is smaller only in proof content.  The construction of `EnclosedFaceSetSucc` for the new
face set is reduced to a turn check, one position at a time, which
`pinchFollow_outer_follows_iff` shows is exactly `FollowsBoundary`.

**LOUD: what is false.**
* The natural weaker input, "noncrossing plus both Euler equalities gives `FollowsBoundary`", is
  FALSE; see the docstring of `PinchFollowTurn.lean`.
* The candidate `w' = K.walk` (faces `sideFaces K.walk`, walk `invDarts X K.walk`) is not a
  general answer.
  * Its turn condition can fail inside the premise block (scratch `gl-p07-69/lake_grid.py`).
  * When it holds, the dart clause of branch 1 failed in all 6576 grid configurations (scratch
    `gl-p07-69/grid_follow.py`; 6499 of them have an empty arc).
  * The faces of `a` and `b` lie on the side of `K.walk`, because `K.walk` runs along their far
    sides.

So `w'` has to be a new walk, cut to avoid `a`, `b` and the lakes of `K`.  That walk is the
remaining gap.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- The conclusion of `pinchRestDone_ResidualStatement` (lines 83 to 127), verbatim, with
`C.face` as the face `f`. -/
def pinchFollow_Conclusion {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
    {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X)
    (K : CellPocketWalk D eps X i j) (G₁ : CyclicArc (cellDarts X i))
    (G₂ : CyclicArc (cellDarts X j)) (f : X.toCombMap.Face) : Prop :=
  (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
    EnclosedFaceSetSucc X faces outerWalk ∧ f ∈ faces ∧
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
    EnclosedFaceSetSucc X faces outerWalk ∧ f ∈ faces ∧
      ((∃ A : CyclicArc (cellDarts X i),
          invDarts X (outerWalk.rotate n) = invDarts X A.darts) ∨
        (∃ A : CyclicArc (cellDarts X j),
          invDarts X (outerWalk.rotate n) = invDarts X A.darts)))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchFollow_Conclusion

/-- **Remaining gap of lane gl-p07-69.**  The premise block of `pinchRestDone_ResidualStatement`
verbatim, (P) included.  The conclusion is that of the target, or a noncrossing closed walk `w'`
with the exterior face off its side and the outer turn condition such that its side, as an
enclosed face set, gives the target's conclusion.  See the module docstring. -/
def pinchFollow_ResidualStatement : Prop :=
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
          pinchFollow_Conclusion a b K G₁ G₂ C.face ∨
            ∃ (w' : List X.toCombMap.Dart) (_hw' : IsNoncrossingClosedWalk X.toCombMap w'),
              X.outerFace ∉ sideFaces X.toCombMap w' ∧
              pinchFollow_OuterTurn X.toCombMap w' ∧
              (EnclosedFaceSetSucc X (sideFaces X.toCombMap w') (invDarts X w') →
                pinchFollow_Conclusion a b K G₁ G₂ C.face)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchFollow_ResidualStatement

/-- **The `_of_` reduction of lane gl-p07-69.**  The new disjunct gives the old conclusion through
`pinchFollow_enclosed_of_turn`. -/
theorem pinchFollow_residual_of_statement (h : pinchFollow_ResidualStatement.{u, w, v}) :
    pinchRestDone_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase hP with hc | ⟨w', hw', hout', hturn, hk⟩
  · exact hc
  · exact hk (pinchFollow_enclosed_of_turn hw' hout' hturn)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchFollow_residual_of_statement

/-- **Clause (rest) of the pinch case from the gl-p07-69 statement.** -/
theorem pinchFollow_rest_of_statement (h : pinchFollow_ResidualStatement.{u, w, v}) :
    PinchCase.RestStatement.{u, w, v} :=
  pinchRestDone_rest_of_residual (pinchFollow_residual_of_statement h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchFollow_rest_of_statement

/-- **LOUD: the converse.**  The target gives the statement through its first disjunct, so the two
are equivalent as Props. -/
theorem pinchFollow_statement_of_residual (h : pinchRestDone_ResidualStatement.{u, w, v}) :
    pinchFollow_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  exact Or.inl (h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout
    hinner houter C hC hCf hCa hCb hcase hP)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchFollow_statement_of_residual

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
