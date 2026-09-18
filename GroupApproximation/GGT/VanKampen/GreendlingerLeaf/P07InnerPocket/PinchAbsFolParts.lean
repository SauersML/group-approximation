import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsFolStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-79: the two halves of the split residual

Both halves carry the premise block of `pinchAbsFol_ResidualStatement` verbatim, with one extra
premise inserted right after `hw`:
* `pinchAbsFol_FollowPart` (lanes gl-p07-76/77): `(hw.outerCycle X.planar).FollowsBoundary`,
  conclusion `pinchFollow_Conclusion ∨ pinchAbsTouch_Tail`;
* `pinchAbsFol_PinchPart` (lane gl-p07-78): `¬ (hw.outerCycle X.planar).FollowsBoundary`,
  conclusion `pinchFollow_Conclusion ∨ pinchAbs_Cut`.

Endpoints: `pinchAbsFol_statement_of_parts` (the two halves give the residual) and
`pinchAbsFol_off_of_parts` (on to `PocketFourPieceOffStatement`).  Also
`pinchAbsFol_followPart_of_tail`: gl-p07-75's `pinchAbsTouch_TailStatement` gives the follows half
(it is the same conclusion without the `FollowsBoundary` premise), and `pinchAbsFol_off_of_tail`.

**LOUD: logical strength.**  The residual gives each half (`pinchAbsFol_followPart_of_statement`,
`pinchAbsFol_pinchPart_of_statement`), so the conjunction of the halves is EQUIVALENT as a Prop to
`pinchAbsFol_ResidualStatement` (and to the earlier residuals).  Each half on its own is strictly
smaller in proof content: it covers only one side of the `FollowsBoundary` split.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The follows half** (lanes gl-p07-76/77). -/
def pinchAbsFol_FollowPart : Prop :=
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
      (hw.outerCycle X.planar).FollowsBoundary →
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
          pinchFollow_Conclusion a b K G₁ G₂ C.face ∨ pinchAbsTouch_Tail a b K G₁ G₂ C.face

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsFol_FollowPart

/-- **The pinched half** (lane gl-p07-78). -/
def pinchAbsFol_PinchPart : Prop :=
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
      ¬ (hw.outerCycle X.planar).FollowsBoundary →
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
          pinchFollow_Conclusion a b K G₁ G₂ C.face ∨ pinchAbs_Cut a b K G₁ G₂ C.face

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsFol_PinchPart

/-- **The `_of_` reduction to the split residual.**  Split on `FollowsBoundary`; in the follows
case the circuit tail is kept as the first conjunct, in the pinched case the cut as the second. -/
theorem pinchAbsFol_statement_of_parts (hF : pinchAbsFol_FollowPart.{u, w, v})
    (hN : pinchAbsFol_PinchPart.{u, w, v}) : pinchAbsFol_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  by_cases hfo : (hw.outerCycle X.planar).FollowsBoundary
  · rcases hF D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hfo hout
      hinner houter C hC hCf hCa hCb hcase hP with hc | ht
    · exact Or.inl hc
    · exact Or.inr ⟨fun _ => ht, fun hn => absurd hfo hn⟩
  · rcases hN D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hfo hout
      hinner houter C hC hCf hCa hCb hcase hP with hc | hcut
    · exact Or.inl hc
    · exact Or.inr ⟨fun hf => absurd hf hfo, fun _ => hcut⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsFol_statement_of_parts

/-- **P07's top target from the two halves.** -/
theorem pinchAbsFol_off_of_parts (hF : pinchAbsFol_FollowPart.{u, w, v})
    (hN : pinchAbsFol_PinchPart.{u, w, v}) : PocketFourPieceOffStatement.{u, w, v} :=
  pinchAbsFol_off_of_statement (pinchAbsFol_statement_of_parts hF hN)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsFol_off_of_parts

/-- **gl-p07-75's residual gives the follows half** (drop the `FollowsBoundary` premise). -/
theorem pinchAbsFol_followPart_of_tail (h : pinchAbsTouch_TailStatement.{u, w, v}) :
    pinchAbsFol_FollowPart.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw _ hout hinner houter C hC hCf hCa hCb hcase hP
  exact h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase hP

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsFol_followPart_of_tail

/-- **P07's top target from gl-p07-75's residual and the pinched half** (no
`pinchAbsSub_OutsideStatement`). -/
theorem pinchAbsFol_off_of_tail (hT : pinchAbsTouch_TailStatement.{u, w, v})
    (hN : pinchAbsFol_PinchPart.{u, w, v}) : PocketFourPieceOffStatement.{u, w, v} :=
  pinchAbsFol_off_of_parts (pinchAbsFol_followPart_of_tail hT) hN

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsFol_off_of_tail

/-- **LOUD: the residual gives the follows half.** -/
theorem pinchAbsFol_followPart_of_statement (h : pinchAbsFol_ResidualStatement.{u, w, v}) :
    pinchAbsFol_FollowPart.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hfo hout hinner houter C hC hCf hCa hCb hcase hP
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase hP with hc | ⟨ht, -⟩
  · exact Or.inl hc
  · exact Or.inr (ht hfo)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsFol_followPart_of_statement

/-- **LOUD: the residual gives the pinched half.** -/
theorem pinchAbsFol_pinchPart_of_statement (h : pinchAbsFol_ResidualStatement.{u, w, v}) :
    pinchAbsFol_PinchPart.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hfo hout hinner houter C hC hCf hCa hCb hcase hP
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase hP with hc | ⟨-, hcut⟩
  · exact Or.inl hc
  · exact Or.inr (hcut hfo)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsFol_pinchPart_of_statement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
