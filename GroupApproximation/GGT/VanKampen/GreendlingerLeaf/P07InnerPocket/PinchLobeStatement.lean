import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchLobeLemmas
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-71: the lobe cut along the complement circuit

The target is `pinchCut_ResidualStatement` (`PinchCutStatement.lean:198`).  Its new disjunct
`pinchCut_Cut` asks for a face set `F ⊇ P₀ = keepClass a b K f`, lobe-closed (faces of `F` off
`P₀` leave `F` only across `G₁`/`G₂` edges), and a walk `w'` with eight more clauses.

This file fixes `w'`: it is `pinchLobe_walk F comp = invDarts X (circuit (pinchLobe_out F) comp)`,
the reversed boundary circuit `comp` of the complement of `F`.  Five of the clauses are proved for
every such walk (`PinchLobeLemmas.lean`): noncrossing, the darts are boundary darts of `F`, the
outer turn condition, the exterior face off its side (from `SUB`), and `f` on its side (given one
dart of the circuit whose reversal is based in `P₀`, the touch condition).

* `pinchLobe_cut_of_circuit`: lobe-closed `F`, a circuit `comp` of its complement, touch, `SUB`
  and the tail give `pinchCut_Cut`.
* `pinchLobe_cut_of_keepClass`: step 1, the case `F = P₀` (the lobe condition is vacuous).
* `pinchLobe_Cut` bundles the remaining data: `F`, `comp`, `P₀ ⊆ F`, the lobe condition, touch,
  `SUB` and the tail.  `pinchLobe_cutOf` turns it into `pinchCut_Cut`.
* `pinchLobe_ResidualStatement` is the premise block of the target verbatim, (P) included, with
  the conclusion `pinchFollow_Conclusion ∨ pinchLobe_Cut`.  `pinchLobe_cut_of_statement` is the
  `_of_` reduction to `pinchCut_ResidualStatement`, and `pinchLobe_off` carries it to
  `PocketFourPieceOffStatement`.

**Truth check** (python, scratch `gl-p07-71/lobe_check.py`, reusing `gl-p07-70/`).  For
`F = P₀ ∪ lobes` (`m9.absorb`) and each circuit of the complement of `F` with touch, `w'` is the
reversed circuit.  The new disjunct (some such circuit has `SUB` and the tail, the tail checked
without its `EnclosedFaceSetSucc` hypothesis) held in every configuration tried:
* paper models M9 9 of 9, M9big 16 of 16, M11 39 of 39, M11a 39 of 39;
* random grid maps 47683 of 47683 (seed 71, 300 maps, 9 mutations) and 27162 of 27162
  (inner mode, seed 72, 300 maps, 6 mutations).
The five proved clauses (noncrossing, boundary darts, turn, `OFF` given `SUB`, `f` on the side)
held for every circuit with touch, as a check of the Lean proofs.  In M11 the correct `w'` visits
the pinch vertex twice.  It is the reversed circuit of the complement, which is why this route
covers M11 while `pinchCut_cut_of_circuit` (circuits of `P₀` itself) does not.

**LOUD: what fails.**  Step 1 alone, `F = P₀`, holds on all random grid maps (no lobe is ever
absorbed there) but fails on the paper models: the noninterleave clauses in M9 and M9big, and
the arc clause in M11 and M11a.  So lobes are needed, and `F = P₀` is not enough.

**LOUD: logical strength.**  `pinchLobe_ResidualStatement` is EQUIVALENT to the target as a Prop:
the first disjunct is kept (`pinchLobe_statement_of_residual`), and the new disjunct implies
`pinchCut_Cut` (`pinchLobe_cutOf`).  The new disjunct is STRONGER than `pinchCut_Cut`, since `w'` is
fixed to a reversed complement circuit.  It is STRICTLY SMALLER in proof content: noncrossing, the
dart clause, the turn condition, `OFF` and `f ∈ side w'` are proved.  What is left is the choice
of `F` and `comp` (with touch), `SUB` (`side w' ⊆ side K.walk`) and the tail.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- The reversed boundary circuit `comp` of the complement of `F`. -/
noncomputable def pinchLobe_walk (F : Finset X.toCombMap.Face)
    (comp : FaceSetCircuits.Component X.toCombMap (pinchLobe_out X.toCombMap F)) :
    List X.toCombMap.Dart :=
  invDarts X (FaceSetCircuits.circuit X.toCombMap (pinchLobe_out X.toCombMap F) comp)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_walk

/-- **The cut along a complement circuit.**  For lobe-closed `F ⊇ P₀` and a boundary circuit
`comp` of the complement of `F` touching `P₀`, only `SUB` and the tail are left. -/
theorem pinchLobe_cut_of_circuit {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hG₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (hG₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    {F : Finset X.toCombMap.Face} (hsubF : FourPieceWitness.keepClass a b K f ⊆ F)
    (hlobe : ∀ e : X.toCombMap.Dart, X.toCombMap.faceOf e ∈ F →
      X.toCombMap.faceOf e ∉ FourPieceWitness.keepClass a b K f →
      X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ F →
      X.toCombMap.alpha e ∈ G₁.darts ∨ X.toCombMap.alpha e ∈ G₂.darts)
    (comp : FaceSetCircuits.Component X.toCombMap (pinchLobe_out X.toCombMap F))
    (htouch : ∃ x ∈ FaceSetCircuits.circuit X.toCombMap (pinchLobe_out X.toCombMap F) comp,
      X.toCombMap.faceOf (X.toCombMap.alpha x) ∈ FourPieceWitness.keepClass a b K f)
    (hsub : sideFaces X.toCombMap (pinchLobe_walk F comp) ⊆ sideFaces X.toCombMap K.walk)
    (htail : EnclosedFaceSetSucc X (sideFaces X.toCombMap (pinchLobe_walk F comp))
        (invDarts X (pinchLobe_walk F comp)) →
      pinchCut_Tail b G₁ G₂ (invDarts X (pinchLobe_walk F comp))) :
    pinchCut_Cut a b K G₁ G₂ f := by
  obtain ⟨x, hx, hxf⟩ := htouch
  have hmem : X.toCombMap.alpha x ∈ pinchLobe_walk F comp := by
    show X.toCombMap.alpha x ∈
      invDarts X (FaceSetCircuits.circuit X.toCombMap (pinchLobe_out X.toCombMap F) comp)
    rw [Embedded.mem_invDarts_iff, X.toCombMap.alpha_involutive x]
    exact hx
  have hbd : ∀ e ∈ pinchLobe_walk F comp,
      Surgery.MapCollapse.IsBoundaryDart X.toCombMap F e :=
    fun _ he => pinchLobe_bd (comp := comp) he
  exact ⟨F, pinchLobe_walk F comp, hsubF, hlobe, pinchLobe_nc X.planar comp, hbd,
    fun h => hout (hsub h), pinchLobe_turn X.planar comp,
    pinchLobe_side hG₁ hG₂ hsubF hlobe hbd hmem hxf, hsub, htail⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_cut_of_circuit

/-- **Step 1: the case `F = P₀`.**  A boundary circuit of the complement of `P₀` touching `P₀`,
with `SUB` and the tail, gives the cut; the lobe condition is vacuous. -/
theorem pinchLobe_cut_of_keepClass {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hG₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (hG₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (comp : FaceSetCircuits.Component X.toCombMap
      (pinchLobe_out X.toCombMap (FourPieceWitness.keepClass a b K f)))
    (htouch : ∃ x ∈ FaceSetCircuits.circuit X.toCombMap
        (pinchLobe_out X.toCombMap (FourPieceWitness.keepClass a b K f)) comp,
      X.toCombMap.faceOf (X.toCombMap.alpha x) ∈ FourPieceWitness.keepClass a b K f)
    (hsub : sideFaces X.toCombMap (pinchLobe_walk (FourPieceWitness.keepClass a b K f) comp) ⊆
      sideFaces X.toCombMap K.walk)
    (htail : EnclosedFaceSetSucc X
        (sideFaces X.toCombMap (pinchLobe_walk (FourPieceWitness.keepClass a b K f) comp))
        (invDarts X (pinchLobe_walk (FourPieceWitness.keepClass a b K f) comp)) →
      pinchCut_Tail b G₁ G₂
        (invDarts X (pinchLobe_walk (FourPieceWitness.keepClass a b K f) comp))) :
    pinchCut_Cut a b K G₁ G₂ f :=
  pinchLobe_cut_of_circuit hG₁ hG₂ hout (Finset.Subset.refl _)
    (fun _ he hne _ => absurd he hne) comp htouch hsub htail

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_cut_of_keepClass

/-- **The lobe cut.**  A lobe-closed face set `F ⊇ P₀ = keepClass a b K f` and a boundary circuit
`comp` of its complement touching `P₀`, whose reversal `pinchLobe_walk F comp` has its side on the
side of `K.walk` and, as an enclosed face set, satisfies the tail clauses. -/
def pinchLobe_Cut (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    (f : X.toCombMap.Face) : Prop :=
  ∃ (F : Finset X.toCombMap.Face)
    (comp : FaceSetCircuits.Component X.toCombMap (pinchLobe_out X.toCombMap F)),
    FourPieceWitness.keepClass a b K f ⊆ F ∧
    (∀ e : X.toCombMap.Dart, X.toCombMap.faceOf e ∈ F →
      X.toCombMap.faceOf e ∉ FourPieceWitness.keepClass a b K f →
      X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ F →
      X.toCombMap.alpha e ∈ G₁.darts ∨ X.toCombMap.alpha e ∈ G₂.darts) ∧
    (∃ x ∈ FaceSetCircuits.circuit X.toCombMap (pinchLobe_out X.toCombMap F) comp,
      X.toCombMap.faceOf (X.toCombMap.alpha x) ∈ FourPieceWitness.keepClass a b K f) ∧
    sideFaces X.toCombMap (pinchLobe_walk F comp) ⊆ sideFaces X.toCombMap K.walk ∧
    (EnclosedFaceSetSucc X (sideFaces X.toCombMap (pinchLobe_walk F comp))
        (invDarts X (pinchLobe_walk F comp)) →
      pinchCut_Tail b G₁ G₂ (invDarts X (pinchLobe_walk F comp)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_Cut

/-- **A lobe cut is a cut.** -/
theorem pinchLobe_cutOf {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hG₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (hG₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (h : pinchLobe_Cut a b K G₁ G₂ f) : pinchCut_Cut a b K G₁ G₂ f := by
  obtain ⟨F, comp, hsubF, hlobe, htouch, hsub, htail⟩ := h
  exact pinchLobe_cut_of_circuit hG₁ hG₂ hout hsubF hlobe comp htouch hsub htail

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_cutOf

/-- **Remaining gap of lane gl-p07-71.**  The premise block of `pinchCut_ResidualStatement`
(`PinchCutStatement.lean:198-234`) verbatim, (P) included.  The conclusion is that of the target
with `pinchCut_Cut` replaced by the lobe cut `pinchLobe_Cut`.  See the module docstring. -/
def pinchLobe_ResidualStatement : Prop :=
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
          pinchFollow_Conclusion a b K G₁ G₂ C.face ∨ pinchLobe_Cut a b K G₁ G₂ C.face

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_ResidualStatement

/-- **The `_of_` reduction of lane gl-p07-71.**  A lobe cut is a cut (`pinchLobe_cutOf`). -/
theorem pinchLobe_cut_of_statement (h : pinchLobe_ResidualStatement.{u, w, v}) :
    pinchCut_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase hP with hc | hcut
  · exact Or.inl hc
  · exact Or.inr (pinchLobe_cutOf hG₁ hG₂ hout hcut)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_cut_of_statement

/-- **The four-piece off statement from the gl-p07-71 statement.** -/
theorem pinchLobe_off (h : pinchLobe_ResidualStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} :=
  pinchCut_off (pinchLobe_cut_of_statement h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_off

/-- **LOUD: the converse.**  The target of gl-p07-70 gives the statement through its first
disjunct, so `pinchLobe_ResidualStatement`, `pinchCut_ResidualStatement` and
`pinchRestDone_ResidualStatement` are equivalent as Props. -/
theorem pinchLobe_statement_of_residual (h : pinchRestDone_ResidualStatement.{u, w, v}) :
    pinchLobe_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  exact Or.inl (h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout
    hinner houter C hC hCf hCa hCb hcase hP)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchLobe_statement_of_residual

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
