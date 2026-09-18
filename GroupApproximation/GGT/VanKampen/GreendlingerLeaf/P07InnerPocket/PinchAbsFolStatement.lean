import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsOutStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchTail
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-79: the split residual, follows case via one circuit

`pinchAbsFol_ResidualStatement` is the premise block of `pinchAbsOut_ResidualStatement`
(`PinchAbsOutStatement.lean`) verbatim, with the conclusion
`pinchFollow_Conclusion ∨ ((FollowsBoundary → pinchAbsTouch_Tail) ∧
(¬ FollowsBoundary → pinchAbs_Cut))`.

**Wiring (proved here, no false hypothesis).**
* Follows case: `pinchAbsOut_outside_of_follows` (gl-p07-74) proves `pinchAbsSub_Outside X K.walk`
  outright, which is exactly the `hO` that `pinchAbsTouch_follow_of_tail` (gl-p07-75) needs; so
  the tail of ONE circuit with `C.face` on its side gives `pinchFollow_Conclusion`
  (`pinchAbsFol_follow`).  The FALSE `pinchAbsSub_OutsideStatement` is never used.
* Pinched case (`¬ FollowsBoundary`): `pinchAbs_Cut` itself, passed through unchanged.
* `pinchAbsFol_of_statement`: the `_of_` reduction to `pinchAbs_ResidualStatement`;
  `pinchAbsFol_off_of_statement`: on to `PocketFourPieceOffStatement` via `pinchAbs_off`.

**LOUD: Prop-level relationship.**  `pinchAbsOut_ResidualStatement → pinchAbsFol_ResidualStatement`
(`pinchAbsFol_of_out`, via `pinchAbsTouch_tail_of_touchTail`) and conversely
(`pinchAbsFol_out_of_statement`, via `pinchAbsFol_follow`), so the two are EQUIVALENT as Props,
and (like every residual of this chain) equivalent to `pinchRestDone_ResidualStatement`
(`pinchAbsFol_of_residual`).  The new disjunct is FORMALLY WEAKER than `pinchAbsOut_Rest`: in the
follows case clause (a) is dropped and (c) becomes one existential circuit with `C.face` on its
side (`pinchAbsTouch_Tail`); the pinched half is unchanged.  The split into the two halves
`pinchAbsFol_FollowPart` / `pinchAbsFol_PinchPart` is in `PinchAbsFolParts.lean`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

section Follow

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Follows case.**  When the outer cycle of `K.walk` follows its boundary, the tail of one
circuit with `f` on its side gives the conclusion (`OUT` is proved, not assumed). -/
theorem pinchAbsFol_follow {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hf : f ∈ sideFaces X.toCombMap K.walk) (hCa : f ∉ a.1) (hCb : f ∉ b.1)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hfo : (hw.outerCycle X.planar).FollowsBoundary) (ht : pinchAbsTouch_Tail a b K G₁ G₂ f) :
    pinchFollow_Conclusion a b K G₁ G₂ f :=
  pinchAbsTouch_follow_of_tail hf hCa hCb hout (pinchAbsOut_outside_of_follows hw X.planar hfo) ht

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsFol_follow

/-- **The split disjunct gives the conclusion of gl-p07-72.** -/
theorem pinchAbsFol_conclusion {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hf : f ∈ sideFaces X.toCombMap K.walk) (hCa : f ∉ a.1) (hCb : f ∉ b.1)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (h : pinchFollow_Conclusion a b K G₁ G₂ f ∨
      (((hw.outerCycle X.planar).FollowsBoundary → pinchAbsTouch_Tail a b K G₁ G₂ f) ∧
        (¬ (hw.outerCycle X.planar).FollowsBoundary → pinchAbs_Cut a b K G₁ G₂ f))) :
    pinchFollow_Conclusion a b K G₁ G₂ f ∨ pinchAbs_Cut a b K G₁ G₂ f := by
  rcases h with hc | ⟨ht, hcut⟩
  · exact Or.inl hc
  · by_cases hfo : (hw.outerCycle X.planar).FollowsBoundary
    · exact Or.inl (pinchAbsFol_follow hw hf hCa hCb hout hfo (ht hfo))
    · exact Or.inr (hcut hfo)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsFol_conclusion

end Follow

/-- **Remaining gap of lane gl-p07-79.**  The premise block of `pinchAbsOut_ResidualStatement`
verbatim, with the conclusion `pinchFollow_Conclusion ∨ ((FollowsBoundary → pinchAbsTouch_Tail) ∧
(¬ FollowsBoundary → pinchAbs_Cut))`. -/
def pinchAbsFol_ResidualStatement : Prop :=
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
            (((hw.outerCycle X.planar).FollowsBoundary → pinchAbsTouch_Tail a b K G₁ G₂ C.face) ∧
              (¬ (hw.outerCycle X.planar).FollowsBoundary → pinchAbs_Cut a b K G₁ G₂ C.face))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsFol_ResidualStatement

/-- **The `_of_` reduction of lane gl-p07-79.**  In the follows case `OUT` is proved
(`pinchAbsOut_outside_of_follows`) and the tail of one circuit gives the conclusion; in the pinched
case the absorbed lobe cut is given. -/
theorem pinchAbsFol_of_statement (h : pinchAbsFol_ResidualStatement.{u, w, v}) :
    pinchAbs_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  exact pinchAbsFol_conclusion hw hCf hCa hCb hout
    (h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
      houter C hC hCf hCa hCb hcase hP)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsFol_of_statement

/-- **P07's top target** from this statement (no `pinchAbsSub_OutsideStatement`). -/
theorem pinchAbsFol_off_of_statement (h : pinchAbsFol_ResidualStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} :=
  pinchAbs_off (pinchAbsFol_of_statement h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsFol_off_of_statement

/-- **LOUD: the residual of gl-p07-74 gives this one** (clauses (a), (c) give one circuit with
`C.face` on its side, `pinchAbsTouch_tail_of_touchTail`), so this one is no stronger. -/
theorem pinchAbsFol_of_out (h : pinchAbsOut_ResidualStatement.{u, w, v}) :
    pinchAbsFol_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase hP with hc | hr
  · exact Or.inl hc
  · exact Or.inr ⟨fun hfo => pinchAbsTouch_tail_of_touchTail hG₁ hG₂ (hr.1 hfo), hr.2⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsFol_of_out

/-- **LOUD: the converse.**  This statement gives the residual of gl-p07-74: in the follows case
through its first disjunct (`pinchAbsFol_follow`).  So the two are EQUIVALENT as Props. -/
theorem pinchAbsFol_out_of_statement (h : pinchAbsFol_ResidualStatement.{u, w, v}) :
    pinchAbsOut_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase hP with hc | ⟨ht, hcut⟩
  · exact Or.inl hc
  · by_cases hfo : (hw.outerCycle X.planar).FollowsBoundary
    · exact Or.inl (pinchAbsFol_follow hw hCf hCa hCb hout hfo (ht hfo))
    · exact Or.inr ⟨fun hfo' => absurd hfo' hfo, fun _ => hcut hfo⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsFol_out_of_statement

/-- **LOUD: the target of gl-p07-70 gives this statement**, so it is equivalent as a Prop to the
earlier residuals. -/
theorem pinchAbsFol_of_residual (h : pinchRestDone_ResidualStatement.{u, w, v}) :
    pinchAbsFol_ResidualStatement.{u, w, v} :=
  pinchAbsFol_of_out (pinchAbsOut_statement_of_sub (pinchAbsSub_statement_of_residual h))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsFol_of_residual

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
