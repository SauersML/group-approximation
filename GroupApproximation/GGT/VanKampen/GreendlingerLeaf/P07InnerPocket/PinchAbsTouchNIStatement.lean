import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchNIList
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchTail
import GroupApproximation.GGT.VanKampen.SurgeryReclosedVertices
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-76: the NoInterleave clauses of the touch tail

Target: the four `CyclicNoInterleave` clauses of `pinchCut_Tail b G₁ G₂ (invDarts X w')`, for
`w' = pinchLobe_walk F comp`, `F = pinchAbs_set a b K G₁ G₂ C.face` and `C.face ∈ side w'`.  As
a Prop this is `pinchAbsTouchNI_NIStatement`.

The premise block is the one of lane gl-p07-79's `pinchAbsFol_FollowPart`, verbatim, including
`hfo : (hw.outerCycle X.planar).FollowsBoundary`.  It does NOT assume
`pinchAbsSub_OutsideStatement`, which is false in general (lane gl-p07-74).  It then adds
* a circuit `comp` with `C.face` on the side of `w'`;
* `EnclosedFaceSetSucc X (side w') (invDarts X w')`, the hypothesis of the tail.

## The residual: `pinchAbsTouchNI_Statement`

It has the same premises, and its conclusion is the block reading `pinchAbsTouchNI_Blocks`: some
rotation of `w'` reads `U₁ ++ U₂ ++ U₃ ++ U₄`, with blocks `Ḡ₁`, (b or a far side), `Ḡ₂`,
(the other far side).  `pinchAbsTouchNI_ni_of_statement` proves the target from it, by list
combinatorics only (`pinchAbsTouchNI_niPart_of_blocks`).

## LOUD: logical strength

**The residual is STRICTLY STRONGER than the target, and it is not an equivalent restatement.**
* `Blocks → NIPart` is proved.
* The converse fails.  The cyclic word `G2 A G1 A` satisfies all four NoInterleave facts but has
  no block reading.  Here `A` means off `G₁`, `G₂` and the b far side.
* The weaker reading with `U₂`, `U₄` each only UNIFORM (all b far side, or none) is EQUIVALENT to
  the four facts, as a statement about cyclic words.  So it was NOT chosen.
* What the residual saves is proof content, not strength.  The class bookkeeping and the cyclic
  interval combinatorics are proved.  What is left is the planar reading step: `w'` runs along
  the rim `Ḡ₁ · (a far side) · Ḡ₂ · (b far side)` blockwise.  This is Jordan-type content (R1)
  and is not attempted here.  Lane gl-p07-17's docstring (`NoninterleaveStatement.lean`) sketches
  it in the dual.

## Truth check (`$SP/gl-p07-76/ni_check.py`)

The script reuses lane gl-p07-75's `touch_check` machinery (`AB.models`, `AB.grids`).  It checks
EVERY boundary circuit of the complement of `F` with `C.face` on its side, without the
`EnclosedFaceSetSucc` hypothesis.
* **Paper models** M9, M9big, M11, M11a: 103 circuits.  NI holds in all 103, and so does the
  block reading.  In 75 of them `w'` visits a vertex twice (M11 style pinch), and all 75 still
  read in blocks.
* **Random grids** (seeds 71, 72, 73): 49974 + 23433 + 73029 circuits.  NI and the block reading
  hold in all of them.
* **Orientation.**  Always `1* A* 2* B*`: after `Ḡ₁` comes the a far side.  This is the second
  disjunct of `Blocks`.  The residual keeps both orientations, so no convention is at stake.
* **Sanity.**  The UNIFORM reading and NI agree in every case.
* **Follows.**  Every case reached had an edge connected outside, which is the consequence of
  `hfo` (`pinchAbsOut_outside_of_follows`).  The python does not evaluate `FollowsBoundary`
  itself.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Residual of lane gl-p07-76: the touch circuit reads in blocks.**  The premises are those of
`pinchAbsFol_FollowPart`, plus a circuit `comp` of the complement of `F = pinchAbs_set …` with
`C.face` on the side of `w' = pinchLobe_walk F comp`, and the enclosed hypothesis of the tail.
The conclusion is `pinchAbsTouchNI_Blocks` for the list of `pinchCut_Tail`.

**LOUD: STRICTLY STRONGER than `pinchAbsTouchNI_NIStatement`**; see the module docstring. -/
def pinchAbsTouchNI_Statement : Prop :=
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
        ∀ comp : FaceSetCircuits.Component X.toCombMap
            (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ C.face)),
          C.face ∈ sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ C.face) comp) →
          EnclosedFaceSetSucc X
              (sideFaces X.toCombMap (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ C.face) comp))
              (invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ C.face) comp)) →
          pinchAbsTouchNI_Blocks b G₁ G₂
            (invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ C.face) comp))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchNI_Statement
