import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchArcStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchJumpLemmas
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-83: the arc residual from the no-wedge residual

* `pinchAbsTouchJump_ow_eq`: the outside walk `invDarts X (pinchLobe_walk F comp)` is the circuit
  `c = FaceSetCircuits.circuit X.toCombMap (pinchLobe_out X.toCombMap F) comp` itself.
* `pinchAbsTouchJump_Statement`: the residual.  Its premises are those of lane gl-p07-77's
  `pinchAbsTouchArc_Statement`, verbatim.  The conclusion is `pinchAbsTouchJump_Free` for `G₁` and
  for `G₂` along `c`, with `H` the complement of `pinchAbs_set a b K G₁ G₂ C.face` and
  `Kw = K.walk`.
* `pinchAbsTouchJump_arc_of_statement`: the residual gives `pinchAbsTouchArc_Statement`, by
  `pinchAbsTouchJump_run_of_free`, with `hw` and `pinchLobe_mem_walk_one`/`_two`.
* `pinchAbsTouchJump_followPart_of`: with lane gl-p07-76's `pinchAbsTouchNI_NIStatement`, it gives
  `pinchAbsFol_FollowPart` (through `pinchAbsTouchArc_followPart_of`).

Neither uses `pinchAbsSub_OutsideStatement`, `pinchAbs_Cut` or `pinchAbsFol_PinchPart`.

## Strength of the residual (LOUD: EQUIVALENT)

`pinchAbsTouchJump_Free` for `G₁, G₂` along `c` is **logically equivalent** to
`pinchAbsTouchArc_Run` for `G₁, G₂` along `ow = c`, as a Prop, under the premises.  One direction is
`pinchAbsTouchJump_run_of_free`.  For the other, the wedge contains `y ∈ c` (so `y` is kept) and
`facePerm x` unkept, so `Run` (which gives `facePerm x = y`) rules the wedge out.  So this is
**not** strictly weaker in logical strength; like `pinchAbsTouchArc_Statement` it is an equivalent
reduction.  It is strictly smaller in proof content only.  Proved here and in
`PinchAbsTouchJumpLemmas.lean`:
* `ow` is the `pinchLobe_out` circuit `c` (the double reversal cancels);
* adjacent darts of every rotation of `c` are joined by a `BoundaryWalk` of `H`;
* the jump is a genuine wedge: `y = σ^(n+1) (α x)`, `n ≥ 1`, and the `n` wedge darts are internal
  to `H` (so their faces lie in `pinchAbs_set`);
* if `facePerm x ∈ G`, a wedge dart `σ^k (α x)`, `1 < k ≤ n`, lies on `K.walk`
  (first kept dart after `facePerm x`, `turn_mem`, `alpha_not_mem`).

What is left: such a wedge between two adjacent darts of `c` inside `G₁` (or `G₂`) never occurs,
off one wrap-around pair if `c` lies inside the arc.  This is Jordan-type content (the pinched
cell's two loops at the pinch vertex, and which side of them the absorbed set lies on), which
`EnclosedFaceSetSucc` and the block reading of lane gl-p07-80 do not supply.

## Truth check

No separate script (the chain was parked first).  Since `Free` and `Run` are equivalent under the
premises (above), lane gl-p07-77's `gl-p07-77/arc_check.py` results carry over: `Run` holds on
103 models and on grids 71, 72 and 73.

## Chain status (LOUD: PARKED)

Lane gl-p07-81 found that the top target of this chain,
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement` (through `PocketFourPieceOffStatement`), is
**false** on the GL03BPinch model.  Its corrected version is proved separately as
`GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected`.  The reductions here are
proved, but the chain they serve is parked.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7 (the inner pocket).  It certifies
no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The outside walk is the circuit.** -/
theorem pinchAbsTouchJump_ow_eq {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (X : DiscDiagram.{u, w, v} W)
    (F : Finset X.toCombMap.Face)
    (comp : FaceSetCircuits.Component X.toCombMap (pinchLobe_out X.toCombMap F)) :
    invDarts X (pinchLobe_walk F comp) =
      FaceSetCircuits.circuit X.toCombMap (pinchLobe_out X.toCombMap F) comp := by
  unfold pinchLobe_walk
  exact pinchAbsTouchArc_invInv X _

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchJump_ow_eq

/-- **Residual: no wedge between adjacent circuit darts inside `G₁` or `G₂`.**  The premises are
those of `pinchAbsTouchArc_Statement`, verbatim.  The conclusion is `pinchAbsTouchJump_Free` for
both arcs along the circuit `comp` of the complement of `pinchAbs_set a b K G₁ G₂ C.face`.  Under
the premises it is equivalent to `pinchAbsTouchArc_Statement`'s conclusion as a Prop, but strictly
smaller in proof content: see the module docstring. -/
def pinchAbsTouchJump_Statement : Prop :=
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
          pinchAbsTouchJump_Free X.toCombMap
              (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ C.face)) K.walk G₁.darts
              (FaceSetCircuits.circuit X.toCombMap
                (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ C.face)) comp) ∧
            pinchAbsTouchJump_Free X.toCombMap
              (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ C.face)) K.walk G₂.darts
              (FaceSetCircuits.circuit X.toCombMap
                (pinchLobe_out X.toCombMap (pinchAbs_set a b K G₁ G₂ C.face)) comp)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchJump_Statement

/-- **The residual gives lane gl-p07-77's arc residual.** -/
theorem pinchAbsTouchJump_arc_of_statement (h : pinchAbsTouchJump_Statement.{u, w, v}) :
    pinchAbsTouchArc_Statement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hfo hout hinner houter C hC hCf hCa hCb hcase hP comp hside henc
  obtain ⟨h₁, h₂⟩ := h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw
    hfo hout hinner houter C hC hCf hCa hCb hcase hP comp hside henc
  rw [pinchAbsTouchJump_ow_eq X]
  exact ⟨pinchAbsTouchJump_run_of_free X.toCombMap _ comp hw
      (fun _ he => pinchLobe_mem_walk_one hG₁ he) h₁,
    pinchAbsTouchJump_run_of_free X.toCombMap _ comp hw
      (fun _ he => pinchLobe_mem_walk_two hG₂ he) h₂⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchJump_arc_of_statement

/-- **The NoInterleave half and the residual give the follows half.** -/
theorem pinchAbsTouchJump_followPart_of (hNI : pinchAbsTouchNI_NIStatement.{u, w, v})
    (h : pinchAbsTouchJump_Statement.{u, w, v}) : pinchAbsFol_FollowPart.{u, w, v} :=
  pinchAbsTouchArc_followPart_of hNI (pinchAbsTouchJump_arc_of_statement h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchJump_followPart_of

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
