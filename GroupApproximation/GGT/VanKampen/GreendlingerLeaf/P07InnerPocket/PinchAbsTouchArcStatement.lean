import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchArcPart
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchNIArc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchNIFollow
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-77: the arc interface from the pinched-jump residual

* `pinchAbsTouchArc_Statement`: the residual.  Its premises are those of lane gl-p07-76's
  `pinchAbsTouchNI_ArcStatement`, verbatim, including the Follows case `hfo`.  The conclusion is
  `pinchAbsTouchArc_Run` for `G₁` and for `G₂` along `ow = invDarts X w'`, where
  `w' = pinchLobe_walk (pinchAbs_set a b K G₁ G₂ C.face) comp`.
* `pinchAbsTouchArc_arc_of_statement`: the residual gives `pinchAbsTouchNI_ArcStatement`, by
  `pinchAbsTouchArc_arcPart_of_run`.
* `pinchAbsTouchArc_followPart_of`: with lane gl-p07-76's `pinchAbsTouchNI_NIStatement`, it gives
  `pinchAbsFol_FollowPart` (through `pinchAbsTouchNI_followPart_of`).

Neither uses `pinchAbsSub_OutsideStatement`.

## Strength of the residual (LOUD)

Given the `EnclosedFaceSetSucc` hypothesis `henc`, `pinchAbsTouchArc_Run` for `G₁, G₂` is
**logically equivalent** to `pinchAbsTouchNI_ArcPart G₁ G₂ ow`, as a Prop.  One direction is
`pinchAbsTouchArc_arcPart_of_run`.  For the other, arcs are face chains, so a jump inside a run
would break the arc that the run is.  So this is **not** strictly weaker in logical strength.
It is strictly smaller in proof content.  Proved here, in `PinchAbsTouchArcLemmas.lean` and
`PinchAbsTouchArcPart.lean`:
* all the list combinatorics: the `invDarts` reversal of rotations and splits, and cyclic indices;
* every adjacent pair at a kept successor (`PocketRun.succ_eq_facePerm_of_keep`);
* every adjacent pair at a pinch-free dart (`PocketRun.succ_eq_facePerm_of_pinchFree`);
* the arc construction from a duplicate-free face chain (`PocketRun.exists_cyclicArc_of_isChain`).

What is left is only: at a **pinched** dart `x` of `G₁` (or `G₂`) whose face successor is **not
kept** by `ow`, the next dart of `ow` inside `G₁` is `facePerm x`.  If `ow` lies wholly inside the
arc, this is required only off one wrap-around pair.  This is the Jordan-type content that
`EnclosedFaceSetSucc` does not provide.  Lane gl-p07-80's block reading (`U₁ ⊆ G₁`, `U₃ ⊆ G₂`)
gives contiguity of the blocks, but not this face-permutation adjacency.

## Truth check

Python, scratch `gl-p07-77/arc_check.py`.  It checks the clauses and `Run` on every circuit `comp`
with `C.face` on the side of `w'`, and checks `Run = ArcPart`.  All true:
* 103 models, of which 75 revisit a dart (M11 style), with 3 all-in-`G₁` wrap-jump cases;
* 30768 cases on grid 72, 67596 on grid 71, and 100350 on grid 73.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7 (the inner pocket).  It certifies
no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Residual: no pinched unkept jump inside `G₁` or `G₂`.**  The premises are those of
`pinchAbsTouchNI_ArcStatement`, verbatim.  The conclusion is `pinchAbsTouchArc_Run` for both arcs
along `invDarts X w'`.  Given the enclosed hypothesis it is equivalent to the arc part as a Prop,
but strictly smaller in proof content: see the module docstring. -/
def pinchAbsTouchArc_Statement : Prop :=
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
          pinchAbsTouchArc_Run X.toCombMap G₁.darts
              (invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ C.face) comp)) ∧
            pinchAbsTouchArc_Run X.toCombMap G₂.darts
              (invDarts X (pinchLobe_walk (pinchAbs_set a b K G₁ G₂ C.face) comp))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchArc_Statement

/-- **The residual gives lane gl-p07-76's arc interface.** -/
theorem pinchAbsTouchArc_arc_of_statement (h : pinchAbsTouchArc_Statement.{u, w, v}) :
    pinchAbsTouchNI_ArcStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hfo hout hinner houter C hC hCf hCa hCb hcase hP comp hside henc
  obtain ⟨h₁, h₂⟩ := h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw
    hfo hout hinner houter C hC hCf hCa hCb hcase hP comp hside henc
  exact pinchAbsTouchArc_arcPart_of_run henc G₁ G₂ h₁ h₂

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchArc_arc_of_statement

/-- **The NoInterleave half and the residual give the follows half.** -/
theorem pinchAbsTouchArc_followPart_of (hNI : pinchAbsTouchNI_NIStatement.{u, w, v})
    (h : pinchAbsTouchArc_Statement.{u, w, v}) : pinchAbsFol_FollowPart.{u, w, v} :=
  pinchAbsTouchNI_followPart_of hNI (pinchAbsTouchArc_arc_of_statement h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchArc_followPart_of

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
