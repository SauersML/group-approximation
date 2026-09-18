import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalResidualLists
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalSideBound
import GroupApproximation.Meta.AxiomGuard

/-!
# The residual contiguity clauses from an in-order block statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-12b.

`P10ExtremalContig.RoseExtremalContigResidualStatement` asks for a witness
`r, source, kept, t₁, t₂, s₁, s₂` of fourteen clauses.  Most of them are list combinatorics once
the kept darts of the region move are read *in the cyclic order of `K.boundary.cycle`*.  The
split is:

* (a) proved here and in `Piece10Live/ExtremalResidualLists`: build `t₁` as the sub-arc of
  `K.sourceArc` reading its kept block (`P07InnerPocket.CyclicArc.subArcArc`), `t₂` as the
  non-wrapping sub-arc of `K.targetArc` reading its kept block (`noWrapSubArc`), and put
  `s₁ := K.firstSide.filter p`, `s₂ := K.secondSide.filter p`.  Then the listing
  `s₁ ++ t₁⁻¹ ++ s₂ ++ t₂` *equals* `K.boundary.cycle.filter p` (`filter_decomposition`, using
  that `p = movePred` is `alpha`-invariant), which gives the permutation and non-emptiness
  clauses; the two chain and three junction clauses come from splitting one chain by
  `List.isChain_append`; properness of `t₁` and the positional containment of `t₂` are `omega`;
  the side clause holds in its first disjunct by `List.mem_filter`.
* (b) `RoseExtremalBlockStatement` (OPEN, PLAUSIBLE): under the same premises, some region `r` and
  kept cell satisfy `ExtremalBlockClauses`: clauses 1-3 of the residual (the class avoids the
  exterior face, the source face is not flipped, the kept face is flipped), the kept darts
  `K.boundary.cycle.filter p` are non-empty and form a walk *in cycle order*, the kept darts of
  `K.sourceArc` form one contiguous block, and the kept darts of `K.targetArc` form one
  contiguous block not starting past the base point (`TargetBlockNoWrap`).
* `contigResidual_of_block` (proved): (b) gives the residual statement.  Corollaries
  `contiguity_of_block` and `outerPinchStep_of_block` chain it through the existing reductions.

## Why (b) is strictly smaller

The residual statement needs the constructions of two cyclic arcs, a permutation, a five-way
chain split, properness and positional bounds, and side membership; (b) keeps only the planar
content: the choice of the region, the in-order walk property of the kept darts, and the block
shape of the kept darts on each arc.  It carries no arc, no permutation and no side data.

## Truth check

Exhaustive search over rose configurations in the model of `gl-p10-11a/contig_search.py`, reading
the kept darts in cycle order with contiguous arc blocks and requiring the in-order chain and a
non-empty listing (scratchpad `gl-p10-12b/inorder_search.py`, mode `inorder`): 542
configurations with at most five petals and 9010 with at most six, 0 violations.  The stronger
shape "the removed darts form one cyclic interval" is false in the model (30 bad
configurations, e.g. single-vertex loop roses) and is not used.  The search does not model least
area, labels, `Unpinched`, or genuine cell structure.

## Wrap risk (reported, lane gl-p10-12a audits it)

`TargetBlockNoWrap K pre` asks `K.targetArc.start + |pre| ≤ |outerDarts X|`: the kept target block
does not start past the base point of the outer cycle.  It is automatic when `pre = []` (for
instance when the block is empty, where `pre = []`, `post = K.targetArc.darts` works) and when the
target arc does not wrap.  It fails only for a wrapping target arc whose extremal region removes a
prefix reaching past the base point; the residual statement carries the same risk through its
clause `K.targetArc.start ≤ t₂.start`, `t₂.start ≤ |outerDarts X|`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section Clauses

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The kept darts of the region move at `r`.** -/
noncomputable def keptPred (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) :
    X.toCombMap.Dart → Bool :=
  movePred X.toCombMap (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r)

/-- **No wrap of the kept target block**: the block skipping `pre` darts of `K.targetArc` starts
at or before the base point of the outer cycle. -/
def TargetBlockNoWrap (K : PocketFaceSet D eps X lo hi) (pre : List X.toCombMap.Dart) : Prop :=
  K.targetArc.start.1 + pre.length ≤ (outerDarts X).length

/-- **The in-order block clauses of an extremal region.** -/
def ExtremalBlockClauses (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
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
    K.targetArc.darts.filter (keptPred K r) = mid ∧ TargetBlockNoWrap K pre)

end Clauses

/-- **The in-order block statement** (OPEN, PLAUSIBLE; the planarity core of the residual
contiguity statement).  Under the premises of `RoseExtremalCoreStatement`, some region `r` and
kept cell satisfy `ExtremalBlockClauses`. -/
def RoseExtremalBlockStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ (r : X.toCombMap.Dart) (kept : Fin X.rCellCount), ExtremalBlockClauses K r kept

/-- **The residual contiguity statement from the in-order block statement.** -/
theorem contigResidual_of_block (h : RoseExtremalBlockStatement.{u, w, v}) :
    P10ExtremalContig.RoseExtremalContigResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, kept, hrout, hsource, hkept, hne, hch, ⟨pre₁, mid₁, post₁, hs₁, hf₁⟩,
      ⟨pre₂, mid₂, post₂, hs₂, hf₂, hnw⟩⟩ :=
    h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
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

/-- **The contiguity statement from the in-order block statement.** -/
theorem contiguity_of_block (h : RoseExtremalBlockStatement.{u, w, v}) :
    P10ExtremalSplit.RoseExtremalContiguityStatement.{u, w, v} :=
  P10ExtremalContig.contiguity_of_contigResidual (contigResidual_of_block h)

/-- **The outer pinch step section from the in-order block statement.** -/
theorem outerPinchStep_of_block (h : RoseExtremalBlockStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  Piece10.proof_of_contiguity (contiguity_of_block h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.keptPred
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.TargetBlockNoWrap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.ExtremalBlockClauses
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.RoseExtremalBlockStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.contigResidual_of_block
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.contiguity_of_block
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.outerPinchStep_of_block
