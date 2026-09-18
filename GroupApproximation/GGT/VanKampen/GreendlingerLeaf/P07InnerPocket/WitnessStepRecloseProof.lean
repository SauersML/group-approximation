import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepRecloseCycle
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBridgeStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSkipProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-62: the Reclosed residual from a rotation order

Lane gl-p07-62.  Discharges the face set and the boundary cycle of
`FourPieceWitness.witnessStepBridge_ReclosedStatement`: `O` is the collapsed set (the complement
`univ \ witnessFaces a b K C.face` of the pocket middle) and `B` is a rotation of `outerWalk`
(`WitnessStepRecloseCycle.lean`).  What is left is the order clause, stated as
`FourPieceWitness.witnessStepReclose_OrderStatement`.  Wires the Bridge, the skip residual and the
corner residual from it.  Certifies no printed sentence on its own.  NOT COMPILED: authored
without running Lean.

## The residual

Premise block of `witnessStepBridge_ReclosedStatement`.  With `w = witnessSublistCurve a b G₁ G₂`
and `l = invDarts X outerWalk`: some `r` has, on entries of `l`, the order of `w` equal to the
order of `invDarts X (outerWalk.rotate r)`, a rotation of `l` (`invDarts_rotate`).

## Status (LOUD)

* **Not weaker as a formula.**  The residual implies the Reclosed statement
  (`witnessStepReclose_reclosed_of_order`), so it is at least as strong.  It is smaller only in
  proof content: it has no face set, no boundary cycle and no `FollowsBoundary` clause.
* **The reclosing detour adds no order content.**  For the collapsed set, the boundary darts are
  **exactly** the darts of `outerWalk` (`witnessStepReclose_isBoundary_iff`, from `mem_iff` and
  `hnb`).  So every boundary cycle of it that follows its boundary is a rotation of `outerWalk`,
  and the Reclosed order clause for this `O` is literally this residual.  With another `O` the
  Reclosed formula may be weaker, but no other natural candidate is known.  `O = sideFaces` cannot
  carry the walk, since walk darts on `a.sideFrom j` have their face in `a.1`.
* **It is the forward curve-sublist order.**  When `|l| ≥ 2`, the residual forces every entry of
  `l` onto `w`.  When `w` is also duplicate-free, it says that a rotation of `l` is a sublist of
  `w`.  That is the forward disjunct of `WitnessCurveSublistNondegStatement`, the four-piece
  (Jordan-type) order fact, in the pinched case.  **So the gl-p07-60/61 reclosing chain is circular
  for the order**: it relocates the curve-sublist residual and does not reduce it.
* **Truth.**  Not refuted.  gl-p07-61's check (`SP/gl-p07-61/reclose_check.py`, clause K, 0
  failures) takes the curve to be the inverse reading of the `FollowsBoundary` cycle of the
  collapsed set.  By the exact-boundary lemma, that is the inverse reading of a rotation of the
  walk.  So on its models, K is this residual.  **NOT checked** for the real
  `witnessSublistCurve`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Residual of lane gl-p07-62: the curve has the order of a rotation of the walk.**  The
premises of `witnessStepBridge_ReclosedStatement`.  The conclusion: for some `r`, on entries of
`invDarts X outerWalk`, `witnessSublistCurve a b G₁ G₂` has the order of
`invDarts X (outerWalk.rotate r)`.  LOUD: implies the Reclosed statement, so not weaker as a
formula.  It is smaller in proof content, and it is the forward curve-sublist order. -/
def witnessStepReclose_OrderStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    0 < (a.cellArcList i).length → 0 < (a.cellArcList j).length →
    0 < (b.cellArcList i).length → 0 < (b.cellArcList j).length →
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
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 →
      C.face ∉ b.1 →
      ∀ outerWalk : List X.toCombMap.Dart,
        EnclosedFaceSetSucc X (witnessFaces a b K C.face) outerWalk →
        (∀ d ∈ outerWalk,
          X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K C.face) →
        (∀ e ∈ invDarts X outerWalk,
          e ∈ invDarts X G₁.darts ∨ e ∈ invDarts X G₂.darts ∨
          X.toCombMap.alpha e ∈ a.sideFrom j ∨ X.toCombMap.alpha e ∈ b.sideFrom i) →
        (∃ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
          (invDarts X outerWalk).rotate n = s ++ x :: y :: t ∧
          ¬ WitnessStepCellTurn G₁ G₂ outerWalk y ∧
          ¬ WitnessStepSideTurn a b G₁ G₂ outerWalk y ∧
          ¬ WitnessStepBlockTurn a b G₁ G₂ x y ∧
          ¬ WitnessStepCornerTurn a b G₁ G₂ outerWalk y ∧
          WitnessStepPinchOffAt a b K C.face G₁ G₂ outerWalk x y) →
        ∃ r : ℕ, ∀ c ∈ invDarts X outerWalk, ∀ d ∈ invDarts X outerWalk,
          (WitnessStepGenusBefore (witnessSublistCurve a b G₁ G₂) c d ↔
            WitnessStepGenusBefore (invDarts X (outerWalk.rotate r)) c d)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepReclose_OrderStatement

/-- **Lane gl-p07-62: the Reclosed residual from the rotation order.**  `O` is the collapsed set
`univ \ witnessFaces a b K C.face`.  `B` is `outerWalk.rotate r` as a boundary cycle of `O`: its
darts are exactly the boundary darts, and it follows the boundary (`WitnessStepRecloseCycle`). -/
theorem witnessStepReclose_reclosed_of_order (h : witnessStepReclose_OrderStatement.{u, w, v}) :
    witnessStepBridge_ReclosedStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab hpinch
  obtain ⟨r, hr⟩ :=
    h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab hpinch
  have hnb' : ∀ d ∈ outerWalk.rotate r,
      X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K C.face :=
    fun d hd => hnb d (List.mem_rotate.mp hd)
  have E' : EnclosedFaceSetSucc X (witnessFaces a b K C.face) (outerWalk.rotate r) :=
    P07InnerPocket.EnclosedFaceSetSucc.rotate E r
  refine ⟨witnessStepReclose_faces X.toCombMap (witnessFaces a b K C.face),
    witnessStepReclose_cycle E' hnb', witnessStepReclose_followsBoundary E' hnb',
    fun d hd => ?_, ?_⟩
  · show d ∈ outerWalk.rotate r
    exact List.mem_rotate.mpr hd
  · exact hr

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepReclose_reclosed_of_order

/-- **Lane gl-p07-62: the Bridge from the rotation order.** -/
theorem witnessStepReclose_bridge_of_order (h : witnessStepReclose_OrderStatement.{u, w, v}) :
    WitnessStepGenusBridgeStatement.{u, w, v} :=
  witnessStepBridge_of_reclosed (witnessStepReclose_reclosed_of_order h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepReclose_bridge_of_order

/-- **Lane gl-p07-62: the skip residual from the rotation order.** -/
theorem witnessStepReclose_skip_of_order (h : witnessStepReclose_OrderStatement.{u, w, v}) :
    WitnessStepSkipStatement.{u, w, v} :=
  witnessStepBridge_skip_of_reclosed (witnessStepReclose_reclosed_of_order h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepReclose_skip_of_order

/-- **Lane gl-p07-62: the corner residual from the rotation order.** -/
theorem witnessStepReclose_corner_of_order (h : witnessStepReclose_OrderStatement.{u, w, v}) :
    WitnessStepCornerResidualStatement.{u, w, v} :=
  witnessStepCorner_of_witnessStepSkip (witnessStepReclose_skip_of_order h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepReclose_corner_of_order

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
