import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsFolParts
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AssemblyStatement
import GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.Statement
import GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.Cases
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-82: the pinched half, widened by the corrected conclusion

`pinchAbsFol_PinchPart` (`PinchAbsFolParts.lean`) is FALSE on the GL03BPinch model (gl-p07-78).
This file states its widenings.

* `pinchAbsPinchCorr_PinchAll`: the lane's literal target.  The premises are those of
  `pinchAbsFol_PinchPart`, and the conclusion adds the all-cells disjunct
  `pinchAbsPinchCorr_AllCells eps X`: an enclosed face set holding every relator cell, with walk
  length at most `2ε`.
  **LOUD: this is FALSE as well**, on one-cell variants of the GL03BPinch model
  (`scratchpad/gl-p07-82/check.py`, `exact1.py`, `cutv.py`).  In the variant `pendant`, a hexagon
  relator cell `Π_k` hangs off `v` inside the outer face.  In `glued`, `Π_k` is glued to `b` along
  `s₁`.  In `glued2`, a pendant `Π_l` is added as well.
  On all three, every premise holds: `χ = 2`, the walk is noncrossing, the outer face is off the
  side, both reclosed maps have `χ = 2`, the walk does not follow its boundary, and `C` is on the
  side.  `hP` is vacuous, since `witnessFaces = {C, H₁, H₂}` has no successor-form walk.
  The old conclusion fails.  Both branches of `pinchFollow_Conclusion` and `pinchAbs_Cut` have no
  witness under exact enumeration.
  The all-cells disjunct also fails.  A face set holding `Π_k` has at least 8, 6 and 12 boundary
  darts respectively, and every one of them must be on the walk (`mem_iff`).  That is more than
  `2ε = 2`.
* `pinchAbsPinchCorr_PinchPart`: **the corrected true statement.**  The conclusion is widened by
  the whole corrected conclusion `GL03BPinch.TwoArcConclusion eps X`.  On the three variants its
  first disjunct holds: take the off cell `Π_k` with empty arcs and the inner-disc face set, whose
  walk is `s₁⁻¹ s₂⁻¹`.  On the base model the all-cells disjunct holds.
  It follows from `GL03BPinch.InnerPocketEnclosedTwoArcPinchedCorrected`
  (`PinchAbsPinchCorrBridge.lean`).
* `pinchAbsPinchCorr_OffStatement`: `PocketFourPieceOffStatement` (false, gl-p07-81), widened the
  same way.

**LOUD: logical strength.**  Each statement here is strictly weaker than the false statement it
widens (`pinchAbsPinchCorr_pinch_ofOld`, `pinchAbsPinchCorr_off_of_off`).
`pinchAbsPinchCorr_OffStatement` is EQUIVALENT to `GL03BPinch.InnerPocketEnclosedTwoArcCorrected`
(both directions are in `PinchAbsPinchCorrBridge.lean`).
`pinchAbsPinchCorr_PinchPart` is implied by `InnerPocketEnclosedTwoArcPinchedCorrected`.  Its
proof content is only the pinched sub-case, with the extra premises `hcase` and `hP`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The all-cells disjunct**, the second disjunct of `GL03BPinch.TwoArcConclusion`: an enclosed
face set holding every relator cell, with an outer walk of length at most `2ε`. -/
def pinchAbsPinchCorr_AllCells {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (eps : ℕ) (X : DiscDiagram.{u, w, v} W) : Prop :=
  ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
    EnclosedFaceSetSucc X faces outerWalk ∧
      (∀ C' ∈ X.relatorCells, C'.face ∈ faces) ∧ outerWalk.length ≤ eps + eps

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchCorr_AllCells

/-- The all-cells disjunct gives the corrected conclusion. -/
theorem pinchAbsPinchCorr_twoArcAll {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}
    (h : pinchAbsPinchCorr_AllCells eps X) :
    GroupApproximation.Full.GL03BPinch.TwoArcConclusion eps X :=
  Or.inr h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchCorr_twoArcAll

/-- **The lane's literal target: FALSE** (see the module docstring).  These are the premises of
`pinchAbsFol_PinchPart`, and the conclusion adds the all-cells disjunct only.  It is kept only to
record the refutation, and nothing downstream uses it. -/
def pinchAbsPinchCorr_PinchAll : Prop :=
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
          (pinchFollow_Conclusion a b K G₁ G₂ C.face ∨ pinchAbs_Cut a b K G₁ G₂ C.face) ∨
            pinchAbsPinchCorr_AllCells eps X

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchCorr_PinchAll

/-- **The pinched half, corrected (true given `InnerPocketEnclosedTwoArcPinchedCorrected`).**
These are the premises of `pinchAbsFol_PinchPart`, and the conclusion adds the whole corrected
conclusion `GL03BPinch.TwoArcConclusion eps X` (see the module docstring). -/
def pinchAbsPinchCorr_PinchPart : Prop :=
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
          (pinchFollow_Conclusion a b K G₁ G₂ C.face ∨ pinchAbs_Cut a b K G₁ G₂ C.face) ∨
            GroupApproximation.Full.GL03BPinch.TwoArcConclusion eps X

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchCorr_PinchPart

/-- **The four-piece reading, widened by the corrected conclusion.**  The statement is
`PocketFourPieceOffStatement` (false, gl-p07-81), with `GL03BPinch.TwoArcConclusion eps X` as an
extra disjunct.  It is EQUIVALENT to `GL03BPinch.InnerPocketEnclosedTwoArcCorrected`
(`PinchAbsPinchCorrBridge.lean`). -/
def pinchAbsPinchCorr_OffStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    (∃ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
    (∃ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      X.outerFace ∉ sideFaces X.toCombMap K.walk →
      (reclosedMap X.toCombMap (sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (reclosedMap X.toCombMap (sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
        (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart) (n : ℕ)
          (R₁ R₂ : List X.toCombMap.Dart) (A₁ : CyclicArc (cellDarts X i))
          (A₂ : CyclicArc (cellDarts X j)),
          EnclosedFaceSetSucc X faces outerWalk ∧ C.face ∈ faces ∧
            invDarts X (outerWalk.rotate n) =
              R₁ ++ invDarts X A₁.darts ++ R₂ ++ invDarts X A₂.darts ∧
            ((((∀ r ∈ R₁, X.toCombMap.alpha r ∈ a.sideFrom j) ∨
                  (∀ r ∈ R₁, X.toCombMap.alpha r ∈ b.sideFrom i)) ∧
                ((∀ r ∈ R₂, X.toCombMap.alpha r ∈ a.sideFrom j) ∨
                  (∀ r ∈ R₂, X.toCombMap.alpha r ∈ b.sideFrom i))) ∨
              ((∀ r ∈ R₁ ++ R₂,
                  X.toCombMap.alpha r ∈ a.sideFrom j ∨ X.toCombMap.alpha r ∈ b.sideFrom i) ∧
                (A₁.length = 0 ∨ A₂.length = 0))) ∧
            (A₁.length = 0 → A₂.length = 0 →
              ∃ k₀ : Fin X.rCellCount, (cell X k₀).face ∉ faces)) ∨
          GroupApproximation.Full.GL03BPinch.TwoArcConclusion eps X

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchCorr_OffStatement

/-- The literal all-cells widening implies the corrected widening. -/
theorem pinchAbsPinchCorr_pinch_ofAll (h : pinchAbsPinchCorr_PinchAll.{u, w, v}) :
    pinchAbsPinchCorr_PinchPart.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hfo hout hinner houter C hC hCf hCa hCb hcase hP
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hfo hout
    hinner houter C hC hCf hCa hCb hcase hP with hc | hc
  · exact Or.inl hc
  · exact Or.inr (pinchAbsPinchCorr_twoArcAll hc)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchCorr_pinch_ofAll

/-- The old (false) pinched half implies the corrected one, which is therefore weaker. -/
theorem pinchAbsPinchCorr_pinch_ofOld (h : pinchAbsFol_PinchPart.{u, w, v}) :
    pinchAbsPinchCorr_PinchPart.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hfo hout hinner houter C hC hCf hCa hCb hcase hP
  exact Or.inl (h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hfo
    hout hinner houter C hC hCf hCa hCb hcase hP)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchCorr_pinch_ofOld

/-- The old (false) four-piece reading implies the widened one. -/
theorem pinchAbsPinchCorr_off_of_off (h : PocketFourPieceOffStatement.{u, w, v}) :
    pinchAbsPinchCorr_OffStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff
    hinner houter C hC hCf hCa hCb
  exact Or.inl (h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hoff hinner
    houter C hC hCf hCa hCb)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsPinchCorr_off_of_off

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
