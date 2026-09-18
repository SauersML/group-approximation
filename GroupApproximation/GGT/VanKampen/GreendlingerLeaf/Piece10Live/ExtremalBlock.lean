import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalBlockLemmas
import GroupApproximation.Meta.AxiomGuard

/-!
# The core of the in-order block statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-13.

`P10ExtremalResidual.RoseExtremalBlockStatement` asks for a region `r` and a kept cell satisfying
seven clauses (`ExtremalBlockClauses`).  Here:

* (a) proved (`Piece10Live/ExtremalBlockLemmas`, `blockClauses_of_coreClauses`): the non-emptiness
  clause; the chain of the kept darts inside each arc block; the exterior-avoidance clause when
  some target dart is kept; the source clause when some source dart is kept.
* (b) `RoseExtremalBlockCoreStatement` (OPEN, PLAUSIBLE): `ExtremalBlockCoreClauses`, i.e. the
  exterior clause or a kept target dart, the source clause or a kept source dart, the kept face is
  flipped, the kept darts of the two sides are walks, the three junctions of the in-order
  listing `s₁ ++ t₁⁻¹ ++ s₂ ++ t₂` of kept darts, and the two block shapes (with
  `TargetBlockNoWrap`).
* `roseExtremalBlock_of_core` (proved): (b) gives the block statement.
  `core_of_roseExtremalBlock` (proved) is the converse, so (b) is true exactly when the block
  statement is; `outerPinchStep_of_blockCore` chains (b) to the outer pinch step section.

## Why (b) is strictly smaller

(b) drops the non-emptiness clause and the in-block chains, and weakens the exterior and source
clauses to disjunctions; what remains is the choice of the region, the walk property at the sides
and junctions, and the block shapes.

## Truth check (reported loudly)

* The in-order chain and the block shapes are **false for an arbitrary region** `r`.  Rose with a
  middle disc `R` and petals `B₁` at `Q`, `B₂` at `P ≠ Q`, cycle `a₁ b₁ a₂ b₂` (`a₁ : P → Q`
  along `R`, `b₁` closed at `Q`, `a₂ : Q → P`, `b₂` closed at `P`): moving the region `R` keeps
  `b₁ b₂`, which is not a walk.  They hold only for an extremal choice of `r` (moving `B₁`
  works).  No combinatorial lemma about `flipFaces` gives them; they are planarity plus
  extremality, and they stay in (b).
* `TargetBlockNoWrap` is **not refuted**.  The model search (scratchpad `gl-p10-13/wrap_search.py`,
  the model of `gl-p10-12b/inorder_search.py`) found, in all 542 configurations with at most five
  petals and 9010 with at most six, a valid region whose kept target block is a prefix
  (`pre = []`), where `TargetBlockNoWrap` is automatic.  The model does not see the base point,
  least area, labels, or relator cells.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section Clauses

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The core clauses of an extremal region.** -/
def ExtremalBlockCoreClauses (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    (kept : Fin X.rCellCount) : Prop :=
  ((∃ e ∈ K.targetArc.darts, P10ExtremalResidual.keptPred K r e = true) ∨
    ∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
  ((∃ e ∈ K.sourceArc.darts, P10ExtremalResidual.keptPred K r e = true) ∨
    (cell X K.source).face ∉ flipFaces X.toCombMap K.faces
      (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r)) ∧
  (cell X kept).face ∈ flipFaces X.toCombMap K.faces
    (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
  ((K.firstSide.filter (P10ExtremalResidual.keptPred K r)).IsChain fun d e =>
    X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
  ((K.secondSide.filter (P10ExtremalResidual.keptPred K r)).IsChain fun d e =>
    X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
  (∀ x ∈ (K.firstSide.filter (P10ExtremalResidual.keptPred K r)).getLast?,
    ∀ y ∈ (invDarts X (K.sourceArc.darts.filter (P10ExtremalResidual.keptPred K r))).head?,
      X.toCombMap.vertexOf (X.toCombMap.alpha x) = X.toCombMap.vertexOf y) ∧
  (∀ x ∈ (K.firstSide.filter (P10ExtremalResidual.keptPred K r) ++
      invDarts X (K.sourceArc.darts.filter (P10ExtremalResidual.keptPred K r))).getLast?,
    ∀ y ∈ (K.secondSide.filter (P10ExtremalResidual.keptPred K r)).head?,
      X.toCombMap.vertexOf (X.toCombMap.alpha x) = X.toCombMap.vertexOf y) ∧
  (∀ x ∈ (K.firstSide.filter (P10ExtremalResidual.keptPred K r) ++
      invDarts X (K.sourceArc.darts.filter (P10ExtremalResidual.keptPred K r)) ++
      K.secondSide.filter (P10ExtremalResidual.keptPred K r)).getLast?,
    ∀ y ∈ (K.targetArc.darts.filter (P10ExtremalResidual.keptPred K r)).head?,
      X.toCombMap.vertexOf (X.toCombMap.alpha x) = X.toCombMap.vertexOf y) ∧
  (∃ pre mid post : List X.toCombMap.Dart, K.sourceArc.darts = pre ++ mid ++ post ∧
    K.sourceArc.darts.filter (P10ExtremalResidual.keptPred K r) = mid) ∧
  (∃ pre mid post : List X.toCombMap.Dart, K.targetArc.darts = pre ++ mid ++ post ∧
    K.targetArc.darts.filter (P10ExtremalResidual.keptPred K r) = mid ∧
    P10ExtremalResidual.TargetBlockNoWrap K pre)

/-- **The block clauses from the core clauses**, for a pocket in walk order. -/
theorem blockClauses_of_coreClauses (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    {r : X.toCombMap.Dart} {kept : Fin X.rCellCount} (h : ExtremalBlockCoreClauses K r kept) :
    P10ExtremalResidual.ExtremalBlockClauses K r kept := by
  obtain ⟨hout, hsrc, hkept, hs₁c, hs₂c, hj₁, hj₂, hj₃, ⟨pre₁, mid₁, post₁, hs₁, rfl⟩,
      ⟨pre₂, mid₂, post₂, hs₂, rfl, hnw⟩⟩ := h
  have hrout : ∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x := by
    rcases hout with ⟨e, he, hk⟩ | hout
    · exact outerAvoid_of_keptTarget K r he hk
    · exact hout
  have hsource : (cell X K.source).face ∉ flipFaces X.toCombMap K.faces
      (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) := by
    rcases hsrc with ⟨e, he, hk⟩ | hsrc
    · exact source_not_mem_flipFaces_of_keptSource K r he hk
    · exact hsrc
  have hp : ∀ d, P10ExtremalResidual.keptPred K r (X.toCombMap.alpha d) =
      P10ExtremalResidual.keptPred K r d := fun d =>
    P10ExtremalResidual.movePred_alpha X.toCombMap _ d
  have hlist := P10ExtremalResidual.filter_decomposition X (P10ExtremalResidual.keptPred K r) hp
    K.decomposition rfl rfl
  refine ⟨hrout, hsource, hkept, filter_keptPred_ne_nil K r kept hrout hkept, ?_,
    ⟨pre₁, _, post₁, hs₁, rfl⟩, ⟨pre₂, _, post₂, hs₂, rfl, hnw⟩⟩
  rw [hlist]
  exact List.IsChain.append (List.IsChain.append (List.IsChain.append hs₁c
    (isChain_invDarts_block K hK hs₁) hj₁) hs₂c hj₂) (isChain_targetArc_block K hK hs₂) hj₃

/-- **The core clauses from the block clauses** (the converse; no walk hypothesis needed). -/
theorem coreClauses_of_blockClauses (K : PocketFaceSet D eps X lo hi) {r : X.toCombMap.Dart}
    {kept : Fin X.rCellCount} (h : P10ExtremalResidual.ExtremalBlockClauses K r kept) :
    ExtremalBlockCoreClauses K r kept := by
  obtain ⟨hrout, hsource, hkept, -, hch, hblk₁, hblk₂⟩ := h
  have hp : ∀ d, P10ExtremalResidual.keptPred K r (X.toCombMap.alpha d) =
      P10ExtremalResidual.keptPred K r d := fun d =>
    P10ExtremalResidual.movePred_alpha X.toCombMap _ d
  have hlist := P10ExtremalResidual.filter_decomposition X (P10ExtremalResidual.keptPred K r) hp
    K.decomposition rfl rfl
  rw [hlist] at hch
  obtain ⟨h123, -, hj₃⟩ := List.isChain_append.mp hch
  obtain ⟨h12, hs₂c, hj₂⟩ := List.isChain_append.mp h123
  obtain ⟨hs₁c, -, hj₁⟩ := List.isChain_append.mp h12
  exact ⟨Or.inr hrout, Or.inr hsource, hkept, hs₁c, hs₂c, hj₁, hj₂, hj₃, hblk₁, hblk₂⟩

end Clauses

/-- **The core block statement** (OPEN, PLAUSIBLE).  Under the premises of
`P10ExtremalResidual.RoseExtremalBlockStatement`, some region `r` and kept cell satisfy
`ExtremalBlockCoreClauses`. -/
def RoseExtremalBlockCoreStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ (r : X.toCombMap.Dart) (kept : Fin X.rCellCount), ExtremalBlockCoreClauses K r kept

/-- **The block statement from the core block statement.** -/
theorem roseExtremalBlock_of_core (h : RoseExtremalBlockCoreStatement.{u, w, v}) :
    P10ExtremalResidual.RoseExtremalBlockStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, kept, hc⟩ := h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨r, kept, blockClauses_of_coreClauses K hK hc⟩

/-- **The core block statement from the block statement** (the two are equivalent). -/
theorem core_of_roseExtremalBlock (h : P10ExtremalResidual.RoseExtremalBlockStatement.{u, w, v}) :
    RoseExtremalBlockCoreStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, kept, hc⟩ := h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨r, kept, coreClauses_of_blockClauses K hc⟩

/-- **The outer pinch step section from the core block statement.** -/
theorem outerPinchStep_of_blockCore (h : RoseExtremalBlockCoreStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  P10ExtremalResidual.outerPinchStep_of_block (roseExtremalBlock_of_core h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.ExtremalBlockCoreClauses
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.blockClauses_of_coreClauses
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.coreClauses_of_blockClauses
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.RoseExtremalBlockCoreStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.roseExtremalBlock_of_core
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.core_of_roseExtremalBlock
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.outerPinchStep_of_blockCore
