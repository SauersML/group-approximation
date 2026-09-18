import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalWrapCore
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalResidual
import GroupApproximation.Meta.AxiomGuard

/-!
# The in-order block statement without wrap

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-12a (bridge to lane
gl-p10-12b, `Piece10Live/ExtremalResidual`).

Under the premise `hi ≤ |outerDarts X|` the clause `P10ExtremalResidual.TargetBlockNoWrap K pre`
is automatic for every split `K.targetArc.darts = pre ++ mid ++ post`:
`K.targetArc.start + |pre| ≤ K.targetArc.start + K.targetArc.length ≤ hi ≤ |outerDarts X|`.  So the
no-wrap block statement drops that clause.

* `targetBlockNoWrap_of_le` (proved).
* `ExtremalBlockNoWrapClauses`: `P10ExtremalResidual.ExtremalBlockClauses` without
  `TargetBlockNoWrap`.
* `RoseExtremalBlockNoWrapStatement` (OPEN, PLAUSIBLE): the block statement with the premise
  `hi ≤ |outerDarts X|` and the weaker clauses; `blockNoWrap_of_block` (proved) shows it is implied
  by `P10ExtremalResidual.RoseExtremalBlockStatement`.
* `contigResidualNoWrap_of_blockNoWrap` (proved): the body of
  `P10ExtremalResidual.contigResidual_of_block`, pointwise, with the no-wrap clause supplied.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
  P10ExtremalResidual

section Clauses

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **No wrap of any target block** when `hi ≤ |outerDarts X|`. -/
theorem targetBlockNoWrap_of_le (K : PocketFaceSet D eps X lo hi)
    (h : hi ≤ (outerDarts X).length) {pre mid post : List X.toCombMap.Dart}
    (hs : K.targetArc.darts = pre ++ mid ++ post) : TargetBlockNoWrap K pre := by
  have hlen := P07InnerPocket.CyclicArc.length_add_of_darts_eq K.targetArc hs
  have hle := K.le_hi
  show K.targetArc.start.1 + pre.length ≤ (outerDarts X).length
  omega

/-- **The in-order block clauses without the no-wrap clause.** -/
def ExtremalBlockNoWrapClauses (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    (kept : Fin X.rCellCount) : Prop :=
  (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
    (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
  (cell X K.source).face ∉ flipFaces X.toCombMap K.faces
    (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
  (cell X kept).face ∈ flipFaces X.toCombMap K.faces
    (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
  K.boundary.cycle.filter (keptPred K r) ≠ [] ∧
  ((K.boundary.cycle.filter (keptPred K r)).IsChain fun d e =>
    X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
  (∃ pre mid post : List X.toCombMap.Dart, K.sourceArc.darts = pre ++ mid ++ post ∧
    K.sourceArc.darts.filter (keptPred K r) = mid) ∧
  (∃ pre mid post : List X.toCombMap.Dart, K.targetArc.darts = pre ++ mid ++ post ∧
    K.targetArc.darts.filter (keptPred K r) = mid)

end Clauses

/-- **The in-order block statement without wrap** (OPEN, PLAUSIBLE): under the premises of
`RoseExtremalCoreNoWrapStatement`, some region `r` and kept cell satisfy
`ExtremalBlockNoWrapClauses`. -/
def RoseExtremalBlockNoWrapStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ (r : X.toCombMap.Dart) (kept : Fin X.rCellCount), ExtremalBlockNoWrapClauses K r kept

/-- **The no-wrap block statement is implied by the block statement.** -/
theorem blockNoWrap_of_block (h : RoseExtremalBlockStatement.{u, w, v}) :
    RoseExtremalBlockNoWrapStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi _ hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, kept, hrout, hsource, hkept, hne, hch, hsrcblock,
      ⟨pre₂, mid₂, post₂, hs₂, hf₂, -⟩⟩ :=
    h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨r, kept, hrout, hsource, hkept, hne, hch, hsrcblock, pre₂, mid₂, post₂, hs₂, hf₂⟩

/-- **The no-wrap residual from the no-wrap block statement**: the body of
`P10ExtremalResidual.contigResidual_of_block`, with `TargetBlockNoWrap` from
`targetBlockNoWrap_of_le`. -/
theorem contigResidualNoWrap_of_blockNoWrap (h : RoseExtremalBlockNoWrapStatement.{u, w, v}) :
    RoseExtremalContigResidualNoWrapStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, kept, hrout, hsource, hkept, hne, hch, ⟨pre₁, mid₁, post₁, hs₁, hf₁⟩,
      ⟨pre₂, mid₂, post₂, hs₂, hf₂⟩⟩ :=
    h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  have hnw : TargetBlockNoWrap K pre₂ := targetBlockNoWrap_of_le K hwrap hs₂
  have hp : ∀ d, keptPred K r (X.toCombMap.alpha d) = keptPred K r d := fun d =>
    movePred_alpha X.toCombMap _ d
  have ht₁ := P07InnerPocket.CyclicArc.subArcArc_darts K.sourceArc pre₁ mid₁ post₁ hs₁
  have ht₂ := noWrapSubArc_darts K.targetArc pre₂ mid₂ post₂ hs₂ hnw
  have hlen₁ := P07InnerPocket.CyclicArc.length_add_of_darts_eq K.sourceArc hs₁
  have hlen₂ := P07InnerPocket.CyclicArc.length_add_of_darts_eq K.targetArc hs₂
  have hlist := (filter_decomposition X (keptPred K r) hp K.decomposition
    (hf₁.trans ht₁.symm) (hf₂.trans ht₂.symm)).symm
  have hchain := hch
  rw [← hlist] at hchain
  obtain ⟨h123, -, hj₃⟩ := List.isChain_append.mp hchain
  obtain ⟨h12, hs₂c, hj₂⟩ := List.isChain_append.mp h123
  obtain ⟨hs₁c, -, hj₁⟩ := List.isChain_append.mp h12
  refine ⟨r, K.source, kept, P07InnerPocket.CyclicArc.subArcArc K.sourceArc pre₁ mid₁ post₁ hs₁,
    noWrapSubArc K.targetArc pre₂ mid₂ post₂ hs₂ hnw, K.firstSide.filter (keptPred K r),
    K.secondSide.filter (keptPred K r), hrout, hsource, hkept, List.Perm.of_eq hlist,
    fun hnil => hne (hlist.symm.trans hnil), hs₁c, hs₂c, hj₁, hj₂, hj₃, ?_, ?_, ?_,
    Or.inl ⟨fun d hd => (List.mem_filter.mp hd).1, fun d hd => (List.mem_filter.mp hd).1⟩⟩
  · show mid₁.length < (cellDarts X K.source).length
    omega
  · show K.targetArc.start.1 ≤ K.targetArc.start.1 + pre₂.length
    omega
  · show K.targetArc.start.1 + pre₂.length + mid₂.length ≤
      K.targetArc.start.1 + K.targetArc.length
    omega

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.targetBlockNoWrap_of_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.ExtremalBlockNoWrapClauses
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.RoseExtremalBlockNoWrapStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.blockNoWrap_of_block
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.contigResidualNoWrap_of_blockNoWrap
