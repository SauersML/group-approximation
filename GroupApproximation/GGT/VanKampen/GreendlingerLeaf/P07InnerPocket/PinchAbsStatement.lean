import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsCut
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-72: the residual with `F = pinchAbs_set`

`pinchAbs_ResidualStatement` is the premise block of `pinchLobe_ResidualStatement`
(`PinchLobeStatement.lean:176`, itself that of `pinchCut_ResidualStatement`) verbatim, (P)
included, with the conclusion `pinchFollow_Conclusion ∨ pinchAbs_Cut`.

* `pinchAbs_lobeCut_of_statement`: the `_of_` reduction to `pinchLobe_ResidualStatement`
  (`pinchAbs_lobeCut_of_cut`: `F := pinchAbs_set`, `P₀ ⊆ F` and the lobe condition proved).
* `pinchAbs_cut_of_statement`: on to `pinchCut_ResidualStatement`; `pinchAbs_off` on to
  `PocketFourPieceOffStatement`.

**What is left** (`pinchAbs_Cut`): a boundary circuit `comp` of the complement of `pinchAbs_set`
with touch, `SUB` (`side w' ⊆ side K.walk`) and the tail, `w' = pinchLobe_walk F comp`.  By
`pinchAbs_cut_of_touch` the touch clause may be supplied by one dart of `P₀` exposed off `F`.

**Truth check** (python, scratch `gl-p07-72/abs_check.py`, a copy of `gl-p07-71/lobe_check.py`).
`abs_lean` is `pinchAbs_set` exactly (rest, bad, reach, `P₀ ∪ (R \ reach)`), tag `PINCHABS`.
* `abs_lean == m9.absorb` in every configuration (`LEAN eq_m9absorb`);
* the lobe clause (proved here) held in every configuration, as a check of `pinchAbs_lobe`;
* the new disjunct `pinchAbs_Cut` (some circuit of the complement with touch, `SUB`, and the tail
  checked WITHOUT its `EnclosedFaceSetSucc` hypothesis, hence a stronger check) held:
  paper models M9 9/9, M9big 16/16, M11 39/39, M11a 39/39 (103/103); random grid maps 47683/47683
  (seed 71, 300 maps, 9 mutations) and 27162/27162 (inner mode, seed 72, 300 maps, 6 mutations).
  It was checked in every configuration, not only those meeting the premises (stronger again).
* in all of them even EVERY touching circuit had `SUB` and the tail (`ALL_TOUCH_GOOD`), and a
  touching dart existed (`LEAN touch_dart`).
* the proved clauses (noncrossing, turn, `f ∈ side`, boundary darts, `OFF` given `SUB`) held.

**LOUD: logical strength.**  `pinchAbs_ResidualStatement` is EQUIVALENT as a Prop to
`pinchLobe_ResidualStatement`, `pinchCut_ResidualStatement` and
`pinchRestDone_ResidualStatement`: it implies them (`pinchAbs_cut_of_statement`) and follows from
the last through its first disjunct (`pinchAbs_statement_of_residual`).  Its new disjunct
`pinchAbs_Cut` is STRONGER than `pinchLobe_Cut` (`F` is fixed to `pinchAbs_set`), and it is
STRICTLY SMALLER in proof content: the choice of `F`, `P₀ ⊆ F` and the lobe condition are done
(`PinchAbsLemmas.lean`), leaving `comp` with touch, `SUB` and the tail.  It is NOT false on any
model tried (see above).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Remaining gap of lane gl-p07-72.**  The premise block of `pinchLobe_ResidualStatement`
verbatim, with the conclusion `pinchFollow_Conclusion ∨ pinchAbs_Cut`. -/
def pinchAbs_ResidualStatement : Prop :=
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
          pinchFollow_Conclusion a b K G₁ G₂ C.face ∨ pinchAbs_Cut a b K G₁ G₂ C.face

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_ResidualStatement

/-- **The `_of_` reduction of lane gl-p07-72.**  An absorbed lobe cut is a lobe cut. -/
theorem pinchAbs_lobeCut_of_statement (h : pinchAbs_ResidualStatement.{u, w, v}) :
    pinchLobe_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase hP with hc | hcut
  · exact Or.inl hc
  · exact Or.inr (pinchAbs_lobeCut_of_cut hcut)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_lobeCut_of_statement

/-- **On to the target of gl-p07-71**, `pinchCut_ResidualStatement`. -/
theorem pinchAbs_cut_of_statement (h : pinchAbs_ResidualStatement.{u, w, v}) :
    pinchCut_ResidualStatement.{u, w, v} :=
  pinchLobe_cut_of_statement (pinchAbs_lobeCut_of_statement h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_cut_of_statement

/-- **The four-piece off statement from the gl-p07-72 statement.** -/
theorem pinchAbs_off (h : pinchAbs_ResidualStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} :=
  pinchLobe_off (pinchAbs_lobeCut_of_statement h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_off

/-- **LOUD: the converse.**  The target of gl-p07-70 gives the statement through its first
disjunct, so `pinchAbs_ResidualStatement` is equivalent as a Prop to the earlier residuals. -/
theorem pinchAbs_statement_of_residual (h : pinchRestDone_ResidualStatement.{u, w, v}) :
    pinchAbs_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  exact Or.inl (h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout
    hinner houter C hC hCf hCa hCb hcase hP)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbs_statement_of_residual

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
