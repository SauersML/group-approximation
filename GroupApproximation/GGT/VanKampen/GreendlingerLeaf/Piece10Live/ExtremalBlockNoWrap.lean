import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalBlock
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalWrapBlock
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalWrapAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# The core of the no-wrap block statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-13 (bridge to lane
gl-p10-12a, `Piece10Live/ExtremalWrapBlock`).

Lane gl-p10-12a observed that `PocketFaceSet.le_hi` does not bound `hi` by `|outerDarts X|`, so
the clause `TargetBlockNoWrap` of `P10ExtremalResidual.RoseExtremalBlockStatement` (and of
`RoseExtremalBlockCoreStatement`, which is equivalent to it) is not guaranteed under its
premises.  It isolated `P10ExtremalWrap.RoseExtremalBlockNoWrapStatement`, with the premise
`hi ≤ |outerDarts X|` and without the wrap clause.  This file reduces that statement to a core in
the same way as `Piece10Live/ExtremalBlock`:

* `RoseExtremalBlockNoWrapCoreStatement` (OPEN, PLAUSIBLE): `ExtremalBlockNoWrapCoreClauses`, the
  clauses of `ExtremalBlockCoreClauses` without `TargetBlockNoWrap`, under the premise
  `hi ≤ |outerDarts X|`.
* `blockNoWrap_of_noWrapCore` (proved), with converse `noWrapCore_of_blockNoWrap` (proved);
  `noWrapCore_of_blockCore` (proved); `contigResidualNoWrap_of_noWrapCore` and
  `relativeGreendlinger_of_noWrapCore` (proved) chain the core to Osin's Lemma 4.4 at least-area
  diagrams through `P10ExtremalWrap.relativeGreendlinger_of_contigResidualNoWrap`.

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

/-- **The core clauses of an extremal region, without the no-wrap clause.** -/
def ExtremalBlockNoWrapCoreClauses (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
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
    K.targetArc.darts.filter (P10ExtremalResidual.keptPred K r) = mid)

/-- **The no-wrap block clauses from the no-wrap core clauses**, for a pocket in walk order with
`hi ≤ |outerDarts X|`. -/
theorem noWrapClauses_of_noWrapCoreClauses (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (hwrap : hi ≤ (outerDarts X).length) {r : X.toCombMap.Dart} {kept : Fin X.rCellCount}
    (h : ExtremalBlockNoWrapCoreClauses K r kept) :
    P10ExtremalWrap.ExtremalBlockNoWrapClauses K r kept := by
  obtain ⟨hout, hsrc, hkept, hs₁c, hs₂c, hj₁, hj₂, hj₃, hblk₁, ⟨pre₂, mid₂, post₂, hs₂, hf₂⟩⟩ :=
    h
  obtain ⟨hrout, hsource, hkept', hne, hch, hblk₁', ⟨pre, mid, post, hs, hf, -⟩⟩ :=
    blockClauses_of_coreClauses (r := r) (kept := kept) K hK
      ⟨hout, hsrc, hkept, hs₁c, hs₂c, hj₁, hj₂, hj₃, hblk₁,
        ⟨pre₂, mid₂, post₂, hs₂, hf₂, P10ExtremalWrap.targetBlockNoWrap_of_le K hwrap hs₂⟩⟩
  exact ⟨hrout, hsource, hkept', hne, hch, hblk₁', pre, mid, post, hs, hf⟩

/-- **The no-wrap core clauses from the no-wrap block clauses** (the converse). -/
theorem noWrapCoreClauses_of_noWrapClauses (K : PocketFaceSet D eps X lo hi)
    {r : X.toCombMap.Dart} {kept : Fin X.rCellCount}
    (h : P10ExtremalWrap.ExtremalBlockNoWrapClauses K r kept) :
    ExtremalBlockNoWrapCoreClauses K r kept := by
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

/-- **The core no-wrap block statement** (OPEN, PLAUSIBLE).  Under the premises of
`P10ExtremalWrap.RoseExtremalBlockNoWrapStatement`, some region `r` and kept cell satisfy
`ExtremalBlockNoWrapCoreClauses`. -/
def RoseExtremalBlockNoWrapCoreStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ (r : X.toCombMap.Dart) (kept : Fin X.rCellCount),
          ExtremalBlockNoWrapCoreClauses K r kept

/-- **The no-wrap block statement from its core.** -/
theorem blockNoWrap_of_noWrapCore (h : RoseExtremalBlockNoWrapCoreStatement.{u, w, v}) :
    P10ExtremalWrap.RoseExtremalBlockNoWrapStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, kept, hc⟩ := h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨r, kept, noWrapClauses_of_noWrapCoreClauses K hK hwrap hc⟩

/-- **The core from the no-wrap block statement** (the two are equivalent). -/
theorem noWrapCore_of_blockNoWrap
    (h : P10ExtremalWrap.RoseExtremalBlockNoWrapStatement.{u, w, v}) :
    RoseExtremalBlockNoWrapCoreStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, kept, hc⟩ := h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨r, kept, noWrapCoreClauses_of_noWrapClauses K hc⟩

/-- **The no-wrap core from the core with the wrap clause.** -/
theorem noWrapCore_of_blockCore (h : RoseExtremalBlockCoreStatement.{u, w, v}) :
    RoseExtremalBlockNoWrapCoreStatement.{u, w, v} :=
  noWrapCore_of_blockNoWrap (P10ExtremalWrap.blockNoWrap_of_block (roseExtremalBlock_of_core h))

/-- **The no-wrap residual contiguity statement from the no-wrap core.** -/
theorem contigResidualNoWrap_of_noWrapCore (h : RoseExtremalBlockNoWrapCoreStatement.{u, w, v}) :
    P10ExtremalWrap.RoseExtremalContigResidualNoWrapStatement.{u, w, v} :=
  P10ExtremalWrap.contigResidualNoWrap_of_blockNoWrap (blockNoWrap_of_noWrapCore h)

/-- **Osin's Lemma 4.4 at least-area diagrams from the four-piece-off residual and the no-wrap
core.** -/
theorem relativeGreendlinger_of_noWrapCore
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : RoseExtremalBlockNoWrapCoreStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  P10ExtremalWrap.relativeGreendlinger_of_contigResidualNoWrap hoff
    (contigResidualNoWrap_of_noWrapCore h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.ExtremalBlockNoWrapCoreClauses
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.noWrapClauses_of_noWrapCoreClauses
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.noWrapCoreClauses_of_noWrapClauses
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.RoseExtremalBlockNoWrapCoreStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.blockNoWrap_of_noWrapCore
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.noWrapCore_of_blockNoWrap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.noWrapCore_of_blockCore
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.contigResidualNoWrap_of_noWrapCore
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.relativeGreendlinger_of_noWrapCore
