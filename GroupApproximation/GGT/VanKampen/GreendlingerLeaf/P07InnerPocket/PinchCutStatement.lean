import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCutLemmas
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchFollowStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-70: cutting the new face set out of the pocket

The target is `pinchFollow_ResidualStatement` (`PinchFollowStatement.lean:107`).  Its second
disjunct asks for a noncrossing closed walk `w'` whose side, as an enclosed face set, gives the
conclusion of `pinchRestDone_ResidualStatement`.  This file pins down which `w'` to take.

Write `Q₀ = PocketClass.pocketKeep a b K` and `P₀ = FourPieceWitness.keepClass a b K c` for the
`Q₀`-class of `c = C.face`.  The candidate is a face set `F ⊇ P₀` whose other faces ("lobes behind
`G`-loops") leave `F` only across edges of `G₁`/`G₂`, with `w'` a boundary circuit of `F` read so
that `F` is on its side.

* `pinchCut_Cut a b K G₁ G₂ c` is that candidate.  It carries the lobe condition and the fact that
  `w'` is made of boundary darts of `F`; the remaining clauses are those of the target's second
  disjunct plus `c ∈ side w'`, `side w' ⊆ side K.walk` and the tail `pinchCut_Tail`.
* `pinchCut_dart_of_lobe` discharges the dart clause of branch 1 of the conclusion from the lobe
  condition: a boundary dart of `P₀` is a `Q₀` dart (`PinchCutLemmas.lean`).
* `pinchCut_follow_of_cut`: a cut gives the second disjunct of the target.
* `pinchCut_cut_of_circuit`: for `F = P₀` and `w'` a `FaceSetCircuits` circuit of `P₀`,
  noncrossing, the boundary darts, the lobe condition and `c ∈ side w'` are proved.
* `pinchCut_ResidualStatement` is the premise block of the target verbatim, (P) included, with the
  conclusion `pinchFollow_Conclusion ∨ pinchCut_Cut`.  `pinchCut_followResidual_of_statement` is
  the `_of_` reduction, and `pinchCut_off` carries it to `PocketFourPieceOffStatement`.

**Truth check** (python, scratch `gl-p07-70/`, `m9.py` and `absw_grid.py`).  The cut with
`F = P₀ ∪ lobes` and `w'` the reversed outer walk of `F` satisfies every clause of `pinchCut_Cut`
(checked as `NEW_DISJ2`) in all configurations tried:
* paper model M9 (empty contact arc of `a`): 9 of 9, and M9big: 16 of 16;
* paper model M11 (branch 2: `Π_i` pinched, a disc of `Π_i` touching the pocket at a vertex):
  39 of 39, and M11a (an `a` lobe inside the disc): 39 of 39;
* random grid maps: 28516 (seed 70), 17115 (pinch mode, seed 71), 9333 (25 mutations, seed 72).
  On the grid maps no lobe is ever absorbed, so `F = P₀` there.

**LOUD: what fails.**
* `F = P₀` alone (every circuit of `P₀`, "KC") fails the noninterleave clauses in M9, and in M11
  its outer circuit fails the arc clause and its inner circuit fails `OFF`.
* `w' = K.walk` ("SIDE") fails the dart clause, since the faces of `b` lie on the side of `K.walk`.
* The python witness face set ("WIT") fails the noninterleave clauses in M9 and has no outer walk
  in 36 of the M11 configurations.
* In M11 the correct `w'` visits the pinch vertex twice.  It is not a `FaceSetCircuits` circuit
  of `P₀`, so `pinchCut_cut_of_circuit` does not cover M11.

**LOUD: logical strength.**  `pinchCut_ResidualStatement` is EQUIVALENT to the target as a Prop:
the first disjunct is kept (`pinchCut_statement_of_residual`) and the new disjunct implies the old
one (`pinchCut_follow_of_cut`).  The new disjunct is STRONGER than the old second disjunct, but
true on all models above.  It is smaller in proof content: the dart clause is proved, and the
choice of `w'` is fixed as `P₀` plus the lobes behind `G`-loops.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- The noninterleave and arc clauses of branch 1 of `pinchFollow_Conclusion`
(`PinchFollowStatement.lean:66-92`), verbatim, for the walk `outerWalk`. -/
def pinchCut_Tail (b : RegionCandidate D eps X) (G₁ : CyclicArc (cellDarts X i))
    (G₂ : CyclicArc (cellDarts X j)) (outerWalk : List X.toCombMap.Dart) : Prop :=
  FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts)
    (invDarts X outerWalk) ∧
  FourPiece.CyclicNoInterleave
    (fun e => e ∉ invDarts X G₁.darts ∧ e ∈ invDarts X G₂.darts)
    (invDarts X outerWalk) ∧
  FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts ∨
    (e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∈ b.sideFrom i))
    (invDarts X outerWalk) ∧
  FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts ∨
    (e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∉ b.sideFrom i))
    (invDarts X outerWalk) ∧
  (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
    (invDarts X outerWalk).rotate m = U ++ V →
    (∀ e ∈ U, e ∈ invDarts X G₁.darts) →
    (∃ e ∈ V, e ∉ invDarts X G₁.darts) →
    ∃ A : CyclicArc (cellDarts X i), U = invDarts X A.darts) ∧
  ((∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₁.darts) →
    ∃ (n : ℕ) (A : CyclicArc (cellDarts X i)),
      invDarts X (outerWalk.rotate n) = invDarts X A.darts) ∧
  (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
    (invDarts X outerWalk).rotate m = U ++ V →
    (∀ e ∈ U, e ∈ invDarts X G₂.darts) →
    (∃ e ∈ V, e ∉ invDarts X G₂.darts) →
    ∃ A : CyclicArc (cellDarts X j), U = invDarts X A.darts) ∧
  ((∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₂.darts) →
    ∃ (n : ℕ) (A : CyclicArc (cellDarts X j)),
      invDarts X (outerWalk.rotate n) = invDarts X A.darts)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchCut_Tail

/-- **The cut.**  A face set `F ⊇ P₀ = keepClass a b K f` whose faces outside `P₀` leave `F` only
across `G₁`/`G₂` edges, and a noncrossing closed walk `w'` of boundary darts of `F`.  The exterior
face is off its side, it satisfies the outer turn condition, `f` is on its side, its side lies on
the side of `K.walk`, and its side as an enclosed face set satisfies the tail clauses. -/
def pinchCut_Cut (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    (f : X.toCombMap.Face) : Prop :=
  ∃ (F : Finset X.toCombMap.Face) (w' : List X.toCombMap.Dart),
    FourPieceWitness.keepClass a b K f ⊆ F ∧
    (∀ e : X.toCombMap.Dart, X.toCombMap.faceOf e ∈ F →
      X.toCombMap.faceOf e ∉ FourPieceWitness.keepClass a b K f →
      X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ F →
      X.toCombMap.alpha e ∈ G₁.darts ∨ X.toCombMap.alpha e ∈ G₂.darts) ∧
    IsNoncrossingClosedWalk X.toCombMap w' ∧
    (∀ e ∈ w', Surgery.MapCollapse.IsBoundaryDart X.toCombMap F e) ∧
    X.outerFace ∉ sideFaces X.toCombMap w' ∧ pinchFollow_OuterTurn X.toCombMap w' ∧
    f ∈ sideFaces X.toCombMap w' ∧ sideFaces X.toCombMap w' ⊆ sideFaces X.toCombMap K.walk ∧
    (EnclosedFaceSetSucc X (sideFaces X.toCombMap w') (invDarts X w') →
      pinchCut_Tail b G₁ G₂ (invDarts X w'))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchCut_Cut

/-- **The dart clause from the lobe condition.**  A boundary dart `e` of `F` is in `invDarts G₁`
or `invDarts G₂`, or is a `Q₀` dart based on the side of `K.walk` off `a` and `b`. -/
theorem pinchCut_dart_of_lobe {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {c : X.toCombMap.Face} {F : Finset X.toCombMap.Face}
    (hCf : c ∈ sideFaces X.toCombMap K.walk) (hCa : c ∉ a.1) (hCb : c ∉ b.1)
    (hsub : FourPieceWitness.keepClass a b K c ⊆ F)
    (hlobe : ∀ e : X.toCombMap.Dart, X.toCombMap.faceOf e ∈ F →
      X.toCombMap.faceOf e ∉ FourPieceWitness.keepClass a b K c →
      X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ F →
      X.toCombMap.alpha e ∈ G₁.darts ∨ X.toCombMap.alpha e ∈ G₂.darts)
    {e : X.toCombMap.Dart} (he : Surgery.MapCollapse.IsBoundaryDart X.toCombMap F e) :
    e ∈ invDarts X G₁.darts ∨ e ∈ invDarts X G₂.darts ∨
      (X.toCombMap.faceOf e ∈ sideFaces X.toCombMap K.walk ∧ X.toCombMap.faceOf e ∉ a.1 ∧
        X.toCombMap.faceOf e ∉ b.1 ∧
        (walkKeep X.toCombMap K.walk e ∨ walkKeep X.toCombMap a.2.boundary.cycle e ∨
          walkKeep X.toCombMap b.2.boundary.cycle e)) := by
  rcases Classical.em (X.toCombMap.faceOf e ∈ FourPieceWitness.keepClass a b K c) with hk | hk
  · have hp := pinchCut_mem_pocketClass hk
    exact Or.inr (Or.inr ⟨PocketClass.mem_sideFaces_of_mem_pocketClass hCf hp,
      PocketClass.not_mem_left_of_mem_pocketClass hCa hp,
      PocketClass.not_mem_right_of_mem_pocketClass hCb hp,
      pinchCut_pocketKeep_of_isBoundaryDart ⟨hk, fun h => he.2 (hsub h)⟩⟩)
  · rcases hlobe e he.1 hk he.2 with h | h
    · exact Or.inl ((Embedded.mem_invDarts_iff G₁.darts e).mpr h)
    · exact Or.inr (Or.inl ((Embedded.mem_invDarts_iff G₂.darts e).mpr h))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchCut_dart_of_lobe

/-- **A cut gives the second disjunct of `pinchFollow_ResidualStatement`.** -/
theorem pinchCut_follow_of_cut {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hCf : f ∈ sideFaces X.toCombMap K.walk) (hCa : f ∉ a.1) (hCb : f ∉ b.1)
    (h : pinchCut_Cut a b K G₁ G₂ f) :
    ∃ (w' : List X.toCombMap.Dart) (_hw' : IsNoncrossingClosedWalk X.toCombMap w'),
      X.outerFace ∉ sideFaces X.toCombMap w' ∧
      pinchFollow_OuterTurn X.toCombMap w' ∧
      (EnclosedFaceSetSucc X (sideFaces X.toCombMap w') (invDarts X w') →
        pinchFollow_Conclusion a b K G₁ G₂ f) := by
  obtain ⟨F, w', hsubF, hlobe, hnc, hbd, hoff, hturn, hf, hsub, htail⟩ := h
  refine ⟨w', hnc, hoff, hturn, fun E => ?_⟩
  unfold pinchFollow_Conclusion
  refine Or.inl ⟨sideFaces X.toCombMap w', invDarts X w', E, hf, hsub, fun d hd => ?_, htail E⟩
  exact pinchCut_dart_of_lobe hCf hCa hCb hsubF hlobe
    (hbd _ ((Embedded.mem_invDarts_iff w' d).mp hd))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchCut_follow_of_cut

/-- **The cut for a circuit of `P₀`.**  For `F = P₀` and `w'` a boundary circuit of `P₀`, only
`OFF`, the turn condition, `SUB` and the tail are left. -/
theorem pinchCut_cut_of_circuit {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (comp : FaceSetCircuits.Component X.toCombMap (FourPieceWitness.keepClass a b K f))
    (hoff : X.outerFace ∉ sideFaces X.toCombMap
      (FaceSetCircuits.circuit X.toCombMap (FourPieceWitness.keepClass a b K f) comp))
    (hturn : pinchFollow_OuterTurn X.toCombMap
      (FaceSetCircuits.circuit X.toCombMap (FourPieceWitness.keepClass a b K f) comp))
    (hsub : sideFaces X.toCombMap
      (FaceSetCircuits.circuit X.toCombMap (FourPieceWitness.keepClass a b K f) comp) ⊆
        sideFaces X.toCombMap K.walk)
    (htail : EnclosedFaceSetSucc X (sideFaces X.toCombMap
        (FaceSetCircuits.circuit X.toCombMap (FourPieceWitness.keepClass a b K f) comp))
      (invDarts X
        (FaceSetCircuits.circuit X.toCombMap (FourPieceWitness.keepClass a b K f) comp)) →
      pinchCut_Tail b G₁ G₂ (invDarts X
        (FaceSetCircuits.circuit X.toCombMap (FourPieceWitness.keepClass a b K f) comp))) :
    pinchCut_Cut a b K G₁ G₂ f :=
  ⟨FourPieceWitness.keepClass a b K f,
    FaceSetCircuits.circuit X.toCombMap (FourPieceWitness.keepClass a b K f) comp,
    Finset.Subset.refl _, fun _ he hne _ => absurd he hne,
    FaceSetCircuits.circuit_isNoncrossingClosedWalk comp,
    fun _ hd => pinchCut_isBoundaryDart_of_mem hd, hoff, hturn,
    pinchCut_mem_sideFaces_of_boundary (FaceSetCircuits.circuit_nonempty _ _ comp)
      (fun _ hd => pinchCut_isBoundaryDart_of_mem hd), hsub, htail⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchCut_cut_of_circuit

/-- **Remaining gap of lane gl-p07-70.**  The premise block of `pinchFollow_ResidualStatement`
(`PinchFollowStatement.lean:108-144`) verbatim, (P) included.  The conclusion is that of the
target, or a cut (`pinchCut_Cut`).  See the module docstring. -/
def pinchCut_ResidualStatement : Prop :=
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
          pinchFollow_Conclusion a b K G₁ G₂ C.face ∨ pinchCut_Cut a b K G₁ G₂ C.face

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchCut_ResidualStatement

/-- **The `_of_` reduction of lane gl-p07-70.**  A cut gives the second disjunct of
`pinchFollow_ResidualStatement` by `pinchCut_follow_of_cut`. -/
theorem pinchCut_followResidual_of_statement (h : pinchCut_ResidualStatement.{u, w, v}) :
    pinchFollow_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase hP with hc | hcut
  · exact Or.inl hc
  · exact Or.inr (pinchCut_follow_of_cut hCf hCa hCb hcut)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchCut_followResidual_of_statement

/-- **`pinchRestDone_ResidualStatement` from the gl-p07-70 statement.** -/
theorem pinchCut_residual_of_statement (h : pinchCut_ResidualStatement.{u, w, v}) :
    pinchRestDone_ResidualStatement.{u, w, v} :=
  pinchFollow_residual_of_statement (pinchCut_followResidual_of_statement h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchCut_residual_of_statement

/-- **Clause (rest) of the pinch case from the gl-p07-70 statement.** -/
theorem pinchCut_rest_of_statement (h : pinchCut_ResidualStatement.{u, w, v}) :
    PinchCase.RestStatement.{u, w, v} :=
  pinchRestDone_rest_of_residual (pinchCut_residual_of_statement h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchCut_rest_of_statement

/-- **The four-piece off statement from the gl-p07-70 statement.** -/
theorem pinchCut_off (h : pinchCut_ResidualStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} :=
  pinchRestDone_off (pinchCut_residual_of_statement h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchCut_off

/-- **LOUD: the converse.**  The target gives the statement through its first disjunct, so
`pinchCut_ResidualStatement` and `pinchRestDone_ResidualStatement` are equivalent as Props. -/
theorem pinchCut_statement_of_residual (h : pinchRestDone_ResidualStatement.{u, w, v}) :
    pinchCut_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  exact Or.inl (h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout
    hinner houter C hC hCf hCa hCb hcase hP)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchCut_statement_of_residual

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
