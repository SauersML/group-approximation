import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlockWitnessAudit
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDart
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabelDart
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-27: step 1 of the corrected four-block residual

Lane gl-p07-27.  The context is Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  This file
proves step 1 of the truth check of gl-p07-24 and isolates the planar reading step as a residual.

## Step 1 (`FourPieceWitness.label_of_witness`)

Every entry `e` of `invDarts X outerWalk` reverses an edge of one of the four arcs of the pocket
curve:
`e ∈ invDarts G₁ ∨ e ∈ invDarts G₂ ∨ α e ∈ a.sideFrom j ∨ α e ∈ b.sideFrom i`.
* `α e` is a dart `d` of `outerWalk`, and `α d = e`.
* `dart_clause` (`FourPieceWitnessDart.lean`, lane gl-p07-21a): `faceOf e` is on the side of `K`,
  off `a` and `b`, and `e` is kept.
* `PocketLabel.label_of_pocket` (`PocketLabelDart.lean`, lane gl-p07-08) gives the label.
This holds without nondegeneracy.  It holds in M9 too, where step 2 fails.

## The residual (`FourPieceWitness.FourBlockNondegLabelStatement`)

This is `FourBlockNondegStatement` (`FourBlockWitnessAudit.lean`), with the step 1 label as an
extra hypothesis after the no-bridge hypothesis.  `fourBlockNondeg_of_label` proves
`FourBlockNondegStatement` from it.

**Smaller: strictly less proof content.**  The extra hypothesis follows from the others
(`label_of_witness`).  So the residual keeps only step 2: at the pinch vertices of the pocket, the
successor orbit of `F` reads a sub-walk of `Γ = Ḡ₁ · Ā · Ḡ₂ · B̄` made of cyclic intervals.  It is
not weaker in logical strength, since the extra hypothesis is provable.

**Truth check.**  TRUE; no counter-model found.  It is equivalent to `FourBlockNondegStatement`;
see the truth check in `FourBlockWitnessAudit.lean`.  M9 does not refute it, since
`0 < (a.cellArcList i).length` fails there.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Step 1: every entry of the reversed witness outside walk reverses an arc of the pocket
curve.**  The arcs are `G₁`, `G₂`, the far side `a.sideFrom j` and the far side `b.sideFrom i`. -/
theorem label_of_witness {a b : RegionCandidate D eps X} {K : CellPocketWalk D eps X i j}
    (hij : i ≠ j) (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j)
    (hfirst : K.firstSide = b.sideFrom j) (hsecond : K.secondSide = a.sideFrom i)
    {G₁ : CyclicArc (cellDarts X i)}
    (h₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    {G₂ : CyclicArc (cellDarts X j)}
    (h₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk) {c : X.toCombMap.Face} (hca : c ∉ a.1)
    (hcb : c ∉ b.1) {outerWalk : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X (witnessFaces a b K c) outerWalk)
    (hnb : ∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K c) :
    ∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₁.darts ∨ e ∈ invDarts X G₂.darts ∨
      X.toCombMap.alpha e ∈ a.sideFrom j ∨ X.toCombMap.alpha e ∈ b.sideFrom i := by
  intro e he
  obtain ⟨hK, ha, hb, hQ⟩ :=
    dart_clause hw hca hcb E hnb _ (PocketLabel.alpha_mem_of_mem_invDarts he)
  rw [X.toCombMap.alpha_involutive e] at hK ha hb hQ
  exact PocketLabel.label_of_pocket hij hai hbi hfirst hsecond h₁ h₂ hw hQ hK ha hb

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.label_of_witness

/-- **Residual of lane gl-p07-27: the planar reading step for nondegenerate candidates.**  This is
`FourBlockNondegStatement` with the step 1 label (`label_of_witness`) as an extra hypothesis.  See
the module docstring. -/
def FourBlockNondegLabelStatement : Prop :=
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
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
      ∀ outerWalk : List X.toCombMap.Dart,
        EnclosedFaceSetSucc X (witnessFaces a b K C.face) outerWalk →
        (∀ d ∈ outerWalk,
          X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K C.face) →
        (∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₁.darts ∨ e ∈ invDarts X G₂.darts ∨
          X.toCombMap.alpha e ∈ a.sideFrom j ∨ X.toCombMap.alpha e ∈ b.sideFrom i) →
        ∃ (n : ℕ) (U₁ U₂ U₃ U₄ : List X.toCombMap.Dart),
          (invDarts X outerWalk).rotate n = U₁ ++ U₂ ++ U₃ ++ U₄ ∧
          (∀ e ∈ U₁, e ∈ invDarts X G₁.darts) ∧
          (∀ e ∈ U₃, e ∉ invDarts X G₁.darts ∧ e ∈ invDarts X G₂.darts) ∧
          (∀ e ∈ U₂, e ∉ invDarts X G₁.darts ∧ e ∉ invDarts X G₂.darts) ∧
          (∀ e ∈ U₄, e ∉ invDarts X G₁.darts ∧ e ∉ invDarts X G₂.darts) ∧
          (((∀ e ∈ U₂, X.toCombMap.alpha e ∈ b.sideFrom i) ∧
              ∀ e ∈ U₄, X.toCombMap.alpha e ∉ b.sideFrom i) ∨
            ((∀ e ∈ U₂, X.toCombMap.alpha e ∉ b.sideFrom i) ∧
              ∀ e ∈ U₄, X.toCombMap.alpha e ∈ b.sideFrom i))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.FourBlockNondegLabelStatement

/-- **The corrected four-block statement from the residual**: supply the step 1 label by
`label_of_witness`. -/
theorem fourBlockNondeg_of_label (h : FourBlockNondegLabelStatement.{u, w, v}) :
    FourBlockNondegStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  exact h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁ hG₁ G₂
    hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
    (label_of_witness hij hai hbi hfirst hsecond hG₁ hG₂ hw hCa hCb E hnb)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.fourBlockNondeg_of_label

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
