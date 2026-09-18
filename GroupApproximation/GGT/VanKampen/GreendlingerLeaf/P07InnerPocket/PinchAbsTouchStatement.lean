import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchTail
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-75: the residual after clauses (a), (c)

`pinchAbsTouch_TailStatement` is the premise block of `pinchAbsSub_TouchTailStatement`
(`PinchAbsSubStatement.lean:73`) verbatim, with the conclusion
`pinchFollow_Conclusion ∨ pinchAbsTouch_Tail` (`PinchAbsTouchTail.lean`): the tail of ONE
boundary circuit of the complement of `pinchAbs_set` having `C.face` on its side.

**Proved in this lane.**  Clause (a) is GONE: given `pinchAbsSub_Outside X K.walk`, the tail of one
circuit with `f` on its side gives `pinchFollow_Conclusion` in every case, sealed or touching
(`pinchAbsTouch_follow_of_tail`); such circuits exist even in the sealed case
(`pinchAbsTouch_exists_side`, via `Embedded.exists_boundaryDart_dualConnected`).  `SUB`,
`EnclosedFaceSetSucc` and the dart clause are proved.  Endpoints:
* `pinchAbsTouch_of_statement`: `Outside → TailStatement → pinchAbsSub_TouchTailStatement`;
* `pinchAbsTouch_sub_of_statement`: `… → pinchAbsSub_ResidualStatement`;
* `pinchAbsTouch_done_of_statement`: `… → pinchRestDone_ResidualStatement` directly;
* `pinchAbsTouch_off_of_statement`: `… → PocketFourPieceOffStatement` (P07's top target).

**Truth check** (python, scratch `gl-p07-75/touch_check.py` on top of `gl-p07-73/sub_check.py`).
For every configuration and EVERY circuit of the complement of `pinchAbs_set` with `f` on its
side, the tail (NI and ARC, checked without its Enclosed hypothesis) holds: 103 model, 47683
(seed 71), 27162 (inner, seed 72), 36344 (seed 73) configurations, all with `OUT` true.  Also
checked: `f ∈ pinchAbs_set`, exterior face off it, touching circuits have `f` on their side, and
exactly ONE circuit has `f` on its side in every configuration.  The sealed case never occurred
(0 of 111292), so the sealed branch of `pinchAbsTouch_follow_of_tail` is untested numerically.

**LOUD: logical strength.**
* As Props, `pinchAbsTouch_TailStatement` is EQUIVALENT to `pinchAbsSub_TouchTailStatement` and
  to the earlier residuals, via `pinchAbsTouch_of_touchTail` and
  `pinchAbsTouch_of_residual`.  The only exception is that the `_of_` reduction also
  needs `pinchAbsSub_OutsideStatement`, which is owned by lane gl-p07-74 and is used as a
  hypothesis.
* Its new disjunct is FORMALLY WEAKER than `pinchAbsSub_TouchTail`
  (`pinchAbsTouch_tail_of_touchTail`): clause (a) is dropped, and (c) becomes one existential
  circuit instead of every touching circuit.
* It is STRICTLY SMALLER in proof content: (a), the sealed case and the touching condition are
  discharged.  What is left is only the tail clauses (`pinchCut_Tail`) for one circuit.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Remaining gap of lane gl-p07-75.**  The premise block of `pinchAbsSub_TouchTailStatement`
verbatim, with the conclusion `pinchFollow_Conclusion ∨ pinchAbsTouch_Tail`. -/
def pinchAbsTouch_TailStatement : Prop :=
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
          pinchFollow_Conclusion a b K G₁ G₂ C.face ∨ pinchAbsTouch_Tail a b K G₁ G₂ C.face

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouch_TailStatement

/-- **The `_of_` reduction of lane gl-p07-75.**  With an edge connected outside, the tail of one
circuit with `C.face` on its side gives the conclusion, so clauses (a), (c) follow. -/
theorem pinchAbsTouch_of_statement (hO : pinchAbsSub_OutsideStatement.{u, w, v})
    (h : pinchAbsTouch_TailStatement.{u, w, v}) :
    pinchAbsSub_TouchTailStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase hP with hc | ht
  · exact Or.inl hc
  · exact Or.inl (pinchAbsTouch_follow_of_tail hCf hCa hCb hout
      (hO X K.walk hw hout hinner houter) ht)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouch_of_statement

/-- **The residual of lane gl-p07-73** from an edge connected outside and this statement. -/
theorem pinchAbsTouch_sub_of_statement (hO : pinchAbsSub_OutsideStatement.{u, w, v})
    (h : pinchAbsTouch_TailStatement.{u, w, v}) :
    pinchAbsSub_ResidualStatement.{u, w, v} :=
  pinchAbsSub_statement_of_split hO (pinchAbsTouch_of_statement hO h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouch_sub_of_statement

/-- **`pinchRestDone_ResidualStatement` directly** from an edge connected outside and this
statement: both disjuncts give `pinchFollow_Conclusion`. -/
theorem pinchAbsTouch_done_of_statement (hO : pinchAbsSub_OutsideStatement.{u, w, v})
    (h : pinchAbsTouch_TailStatement.{u, w, v}) :
    pinchRestDone_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase hP with hc | ht
  · exact hc
  · exact pinchAbsTouch_follow_of_tail hCf hCa hCb hout (hO X K.walk hw hout hinner houter) ht

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouch_done_of_statement

/-- **P07's top target** from an edge connected outside and this statement. -/
theorem pinchAbsTouch_off_of_statement (hO : pinchAbsSub_OutsideStatement.{u, w, v})
    (h : pinchAbsTouch_TailStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} :=
  pinchRestDone_off (pinchAbsTouch_done_of_statement hO h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouch_off_of_statement

/-- **LOUD: clauses (a), (c) give this statement**, so the new disjunct is formally weaker. -/
theorem pinchAbsTouch_of_touchTail (h : pinchAbsSub_TouchTailStatement.{u, w, v}) :
    pinchAbsTouch_TailStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase hP with hc | ht
  · exact Or.inl hc
  · exact Or.inr (pinchAbsTouch_tail_of_touchTail hG₁ hG₂ ht)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouch_of_touchTail

/-- **LOUD: the converse.**  The target of gl-p07-70 gives this statement, so it is equivalent
as a Prop to the earlier residuals. -/
theorem pinchAbsTouch_of_residual (h : pinchRestDone_ResidualStatement.{u, w, v}) :
    pinchAbsTouch_TailStatement.{u, w, v} :=
  pinchAbsTouch_of_touchTail (pinchAbsSub_touchTail_of_residual h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouch_of_residual

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
