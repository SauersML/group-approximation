import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsSubRest
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-73: the residual after `SUB`

`pinchAbsSub_ResidualStatement` is the premise block of `pinchAbs_ResidualStatement`
(`PinchAbsStatement.lean:51`) verbatim, (P) included, with the conclusion
`pinchFollow_Conclusion ∨ pinchAbsSub_Rest`.
* `pinchAbsSub_of_statement`: the `_of_` reduction to `pinchAbs_ResidualStatement`
  (`pinchAbsSub_cut_of_rest`, with `f = C.face ∈ side K` from the premise block).
* The residual splits (`pinchAbsSub_statement_of_split`) into two independent pieces:
  - `pinchAbsSub_OutsideStatement`: for ANY noncrossing closed walk of a disc diagram with the
    outer face off its side and both Euler equalities of the premise block, the outside of the
    walk is edge connected.  It mentions neither `a`, `b`, `G₁`, `G₂`, `C` nor `pinchAbs_set`;
  - `pinchAbsSub_TouchTailStatement`: the premise block with the conclusion
    `pinchFollow_Conclusion ∨ pinchAbsSub_TouchTail`, clauses (a) and (c) only.

**Proved in this lane** (unconditionally): `SUB` for EVERY boundary circuit of the complement of
`pinchAbs_set` from `pinchAbsSub_Outside` (`pinchAbsSub_sub`, plan in `PinchAbsSubSub.lean`), and
towards (a) `pinchAbsSub_sealed`: without a touching dart, every boundary dart of `pinchAbs_set` is
the reversal of a `G₁`/`G₂` dart.

**Truth check** (python, scratch `gl-p07-73/sub_check.py`, on top of `gl-p07-72/abs_check.py`).
`OUT` is `pinchAbsSub_Outside X K.walk` exactly, checked for every pocket walk reached, WITHOUT
the Euler equalities (a stronger check): paper models 8/8 walks, random grids 5608/5608 (seed 71,
300 maps, 9 mutations), 2340/2340 (inner mode, seed 72, 6 mutations), 4708/4708 (seed 73, 12
mutations).  In all configurations (103 model, 47683 + 27162 + 36344 grid): `pinchAbs_set ⊆ side K`,
every dart of `w'` based in `pinchAbs_set`, `SUB` for every circuit (as the proof predicts),
clause (a) and the tail for every touching circuit (`pinchAbsSub_TouchTail`, tail checked without
its `EnclosedFaceSetSucc` hypothesis).  Without the Euler equalities `OUT` is FALSE in general
(two discs meeting at two vertices form a ring whose boundary is one noncrossing closed walk with
a disconnected outside); that ring violates the inner Euler equality (`χ = 1 ≠ 2`), which is
why `pinchAbsSub_OutsideStatement` keeps both equalities.  The grids never produce such a ring,
so the check does not test that the Euler equalities are ENOUGH.

**LOUD: logical strength.**  `pinchAbsSub_ResidualStatement` is EQUIVALENT as a Prop to
`pinchAbs_ResidualStatement` and the earlier residuals: it implies it (`pinchAbsSub_of_statement`)
and follows from `pinchRestDone_ResidualStatement` through its first disjunct
(`pinchAbsSub_statement_of_residual`); the same holds for `pinchAbsSub_TouchTailStatement`.  Its
new disjunct `pinchAbsSub_Rest` implies `pinchAbs_Cut` (given `f ∈ side K`,
`pinchAbsSub_cut_of_rest`), so it is a STRONGER disjunct (it asks the tail of every touching
circuit, and `OUT`).  It is STRICTLY SMALLER in proof content: `SUB` (a statement about
`pinchAbs_set` and a circuit) is replaced by `OUT`, a statement about `K.walk` alone, and the
choice of `comp` is gone.  `pinchAbsSub_OutsideStatement` is a separate, `pinchAbs`-free Prop; it
is NOT implied by anything proved in the repo that I know of.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The outside of a noncrossing closed walk is edge connected**, given the outer face off its
side and both Euler equalities. -/
def pinchAbsSub_OutsideStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (X : DiscDiagram.{u, w, v} W) (walk : List X.toCombMap.Dart)
    (hw : IsNoncrossingClosedWalk X.toCombMap walk),
    X.outerFace ∉ sideFaces X.toCombMap walk →
    (reclosedMap X.toCombMap (sideFaces X.toCombMap walk)
        (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
    (reclosedMap X.toCombMap (sideOutside X.toCombMap walk)
        (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
    pinchAbsSub_Outside X.toCombMap walk

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_OutsideStatement

/-- **Clauses (a) and (c).**  The premise block of `pinchAbs_ResidualStatement` verbatim,
with the conclusion `pinchFollow_Conclusion ∨ pinchAbsSub_TouchTail`. -/
def pinchAbsSub_TouchTailStatement : Prop :=
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
          pinchFollow_Conclusion a b K G₁ G₂ C.face ∨ pinchAbsSub_TouchTail a b K G₁ G₂ C.face

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_TouchTailStatement

/-- **Remaining gap of lane gl-p07-73.**  The premise block of `pinchAbs_ResidualStatement`
verbatim, with the conclusion `pinchFollow_Conclusion ∨ pinchAbsSub_Rest`. -/
def pinchAbsSub_ResidualStatement : Prop :=
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
          pinchFollow_Conclusion a b K G₁ G₂ C.face ∨ pinchAbsSub_Rest a b K G₁ G₂ C.face

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_ResidualStatement

/-- **The `_of_` reduction of lane gl-p07-73.**  The rest gives the absorbed lobe cut. -/
theorem pinchAbsSub_of_statement (h : pinchAbsSub_ResidualStatement.{u, w, v}) :
    pinchAbs_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase hP with hc | hr
  · exact Or.inl hc
  · exact Or.inr (pinchAbsSub_cut_of_rest hCf hr)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_of_statement

/-- **The split**: an edge connected outside (a `pinchAbs`-free statement) and clauses (a), (c)
give the residual. -/
theorem pinchAbsSub_statement_of_split (hO : pinchAbsSub_OutsideStatement.{u, w, v})
    (hT : pinchAbsSub_TouchTailStatement.{u, w, v}) :
    pinchAbsSub_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  rcases hT D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase hP with hc | ht
  · exact Or.inl hc
  · exact Or.inr ⟨hO X K.walk hw hout hinner houter, ht⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_statement_of_split

/-- **LOUD: the converse.**  The target of gl-p07-70 gives the statement through its first
disjunct, so `pinchAbsSub_ResidualStatement` is equivalent as a Prop to the earlier residuals. -/
theorem pinchAbsSub_statement_of_residual (h : pinchRestDone_ResidualStatement.{u, w, v}) :
    pinchAbsSub_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  exact Or.inl (h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout
    hinner houter C hC hCf hCa hCb hcase hP)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_statement_of_residual

/-- **LOUD: the converse for clauses (a), (c).** -/
theorem pinchAbsSub_touchTail_of_residual (h : pinchRestDone_ResidualStatement.{u, w, v}) :
    pinchAbsSub_TouchTailStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  exact Or.inl (h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout
    hinner houter C hC hCf hCa hCb hcase hP)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsSub_touchTail_of_residual

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
