import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalMinimal
import GroupApproximation.Meta.AxiomGuard

/-!
# The in-order block statement, with wrap, from uniform arcs

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-18.

Target of the lane: `P10ExtremalResidual.RoseExtremalBlockStatement`
(`Piece10Live/ExtremalResidual`), the block statement WITH the clause `TargetBlockNoWrap` and
WITHOUT the premise `hi ≤ |outerDarts X|`.  It is NOT closed here.

## Where the tree stood

* `P10ExtremalBlock.RoseExtremalBlockCoreStatement` is proved equivalent to the target
  (`Piece10Live/ExtremalBlock`); no reduction went below it.
* Every deeper reduction (`Piece10Live/ExtremalBlockNoWrap`, `ExtremalRegion`, `ExtremalClass`,
  `ExtremalMinimal`) runs on the NO-WRAP branch: it assumes `hi ≤ |outerDarts X|` and only uses it
  in `P10ExtremalWrap.targetBlockNoWrap_of_le`.  So the wrap branch (a target arc passing the base
  point of the outer cycle, `hi > |outerDarts X|`) had no reduction to the planar core at all.

## What is done here

* `extremalBlock_targetBlockNoWrap_nil` (proved): `TargetBlockNoWrap K []` always holds, since
  `K.targetArc.start : Fin (|outerDarts X| + 1)`.
* `extremalBlock_targetPrefix_of_uniform` (proved): a uniform target arc (all darts kept or all
  removed) has its kept block as a PREFIX, `pre = []`, so the wrap clause is automatic.  This
  removes the wrap risk without any bound on `hi`.
* `extremalBlock_clauses_of_uniform` (proved, pointwise): class choice, linked runs and both arcs
  uniform give `ExtremalBlockClauses K r kept` for some `kept`, for every pocket in walk order.
* `ExtremalBlockUniformStatement` (OPEN, PLAUSIBLE): the conclusion of
  `P10ExtremalRegion.ExtremalMinimalUniformStatement` (lane gl-p10-17's target) under the premises
  of the target, i.e. WITHOUT `hi ≤ |outerDarts X|`.
* `roseExtremalBlock_of_extremalBlockUniform` (proved): the gap gives the target;
  `extremalBlock_outerPinchStep_of_uniform` chains it to `PocketOuterPinchStepSectionStatement`.
* `extremalMinimalUniform_of_extremalBlockUniform` (proved): the gap gives gl-p10-17's target by
  dropping a premise, so the two branches now share ONE planar gap up to the premise on `hi`.

## LOUD: the gap is logically STRONGER than the target, not weaker

A Statement `Q` with a proved `Q → RoseExtremalBlockStatement` that were also logically weaker
would be equivalent to the target, so no strictly weaker gap with an `_of_` reduction exists; the
equivalent core already exists (`RoseExtremalBlockCoreStatement`).  `ExtremalBlockUniformStatement`
is strictly smaller in proof content: it drops the flip face reasoning
(`P10ExtremalRegion.flipClauses_of_avoid`, `P10ExtremalBlock.filter_keptPred_ne_nil`), the chain
assembly (`P10ExtremalRegion.isChain_filter_keptPred_of_stretchesClosed`), the block contiguity
(`P10ExtremalRegion.exists_filter_block_of_noGap`), the position argument
(`P10ExtremalRegion.extremalMinimal_classStretches_of_uniform`) and the whole wrap question.  It
is logically stronger in two ways: uniform arcs are stronger than contiguous blocks, and it has no
premise `hi ≤ |outerDarts X|`, so it is also stronger than `ExtremalMinimalUniformStatement`.

## Truth check

* Lane gl-p10-16's finite model (scratchpad `gl-p10-16/var.py`, mode `allornone`, output
  `gl-p10-16/aon6.txt`): a class with the choice property, linked runs and both arcs uniform
  exists in all 9010 configurations with at most 6 darts, 0 bad.  The model has no base point, so
  it does not distinguish wrapping from non-wrapping target arcs; the clauses of the gap mention
  neither `hi` nor `K.targetArc.start`, and `hi` enters `PocketFaceSet` only through `le_hi`.  So
  dropping `hi ≤ |outerDarts X|` changes nothing the model sees.
* The target arc being a cyclic arc of the outer cycle is invariant under moving the base point;
  wrapping is an artifact of the chosen base position, so no planar argument for the gap can
  depend on the premise.  If lane gl-p10-17 proves its target by a pointwise argument (as every
  existing reduction is), the same proof closes this gap.
* Not refuted; NOT proved.  The model does not see least area, labels or the cell structure.

## Remaining gap

`ExtremalBlockUniformStatement`: the Jordan-type planarity argument choosing a face class of
`walkKeep K.boundary.cycle` with uniform arcs and linked removed runs, the same planar content as
`P10ExtremalRegion.ExtremalMinimalUniformStatement`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section Uniform

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The empty prefix never wraps**: the target arc starts at or before the base point. -/
theorem extremalBlock_targetBlockNoWrap_nil (K : PocketFaceSet D eps X lo hi) :
    TargetBlockNoWrap K [] := by
  have h := K.targetArc.start.isLt
  show K.targetArc.start.1 + 0 ≤ (outerDarts X).length
  omega

/-- **A uniform target arc has its kept block as a prefix**, so the block does not wrap. -/
theorem extremalBlock_targetPrefix_of_uniform (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart)
    (hT : P10ExtremalRegion.ExtremalMinimalArcUniform K r K.targetArc.darts) :
    ∃ pre mid post : List X.toCombMap.Dart, K.targetArc.darts = pre ++ mid ++ post ∧
      K.targetArc.darts.filter (keptPred K r) = mid ∧ TargetBlockNoWrap K pre := by
  have hnw : TargetBlockNoWrap K [] := extremalBlock_targetBlockNoWrap_nil K
  rcases hT with hall | hnone
  · refine ⟨[], K.targetArc.darts, [], ?_, List.filter_eq_self.mpr hall, hnw⟩
    simp
  · refine ⟨[], [], K.targetArc.darts, ?_, ?_, hnw⟩
    · simp
    · exact List.filter_eq_nil_iff.mpr fun x hx => by simp [hnone x hx]

/-- **The block clauses from class choice, linked runs and uniform arcs** (pointwise), for a
pocket in walk order.  No bound on `hi` is used. -/
theorem extremalBlock_clauses_of_uniform (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (r : X.toCombMap.Dart) (hchoice : P10ExtremalRegion.ExtremalClassChoice K r)
    (hlink : P10ExtremalRegion.ExtremalMinimalLinkedRuns K r)
    (hT : P10ExtremalRegion.ExtremalMinimalArcUniform K r K.targetArc.darts)
    (hS : P10ExtremalRegion.ExtremalMinimalArcUniform K r (invDarts X K.sourceArc.darts)) :
    ∃ kept : Fin X.rCellCount, ExtremalBlockClauses K r kept := by
  have hstr : P10ExtremalRegion.ExtremalClassStretches K r :=
    P10ExtremalRegion.extremalMinimal_classStretches_of_uniform K r hlink hT hS
  obtain ⟨kept, hkf, havoid⟩ := P10ExtremalRegion.regionChoice_of_classChoice K r hchoice
  obtain ⟨hrout, hsource, hkept⟩ := P10ExtremalRegion.flipClauses_of_avoid K r kept hkf havoid
  have hne : K.boundary.cycle.filter (keptPred K r) ≠ [] :=
    P10ExtremalBlock.filter_keptPred_ne_nil K r kept hrout hkept
  have hch : (K.boundary.cycle.filter (keptPred K r)).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e :=
    P10ExtremalRegion.isChain_filter_keptPred_of_stretchesClosed K hK r
      (P10ExtremalRegion.stretchesClosed_of_classStretches K hK r hstr)
  have hsblk : ∃ pre mid post : List X.toCombMap.Dart, K.sourceArc.darts = pre ++ mid ++ post ∧
      K.sourceArc.darts.filter (keptPred K r) = mid :=
    P10ExtremalRegion.exists_filter_block_of_noGap (keptPred K r)
      (P10ExtremalRegion.sourceNoGap_of_classStretches K r hstr)
  exact ⟨kept, hrout, hsource, hkept, hne, hch, hsblk,
    extremalBlock_targetPrefix_of_uniform K r hT⟩

end Uniform

/-- **The uniform block statement** (OPEN, PLAUSIBLE; no counterexample in lane gl-p10-16's
model, 9010 configurations).  Under the premises of `RoseExtremalBlockStatement` (no bound on
`hi`), some class `r` has `ExtremalClassChoice`, linked removed runs, and both arcs uniform.
Logically STRONGER than `RoseExtremalBlockStatement` and than
`P10ExtremalRegion.ExtremalMinimalUniformStatement` (see the module docstring). -/
def ExtremalBlockUniformStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ r : X.toCombMap.Dart, P10ExtremalRegion.ExtremalClassChoice K r ∧
          P10ExtremalRegion.ExtremalMinimalLinkedRuns K r ∧
          P10ExtremalRegion.ExtremalMinimalArcUniform K r K.targetArc.darts ∧
          P10ExtremalRegion.ExtremalMinimalArcUniform K r (invDarts X K.sourceArc.darts)

/-- **The block statement (with wrap) from the uniform block statement.** -/
theorem roseExtremalBlock_of_extremalBlockUniform
    (h : ExtremalBlockUniformStatement.{u, w, v}) :
    RoseExtremalBlockStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hchoice, hlink, hT, hS⟩ :=
    h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨kept, hc⟩ := extremalBlock_clauses_of_uniform K hK r hchoice hlink hT hS
  exact ⟨r, kept, hc⟩

/-- **The extremal minimal uniform statement from the uniform block statement** (drop the premise
`hi ≤ |outerDarts X|`): both branches rest on the same planar gap. -/
theorem extremalMinimalUniform_of_extremalBlockUniform
    (h : ExtremalBlockUniformStatement.{u, w, v}) :
    P10ExtremalRegion.ExtremalMinimalUniformStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi _ hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose

/-- **The outer pinch step section from the uniform block statement.** -/
theorem extremalBlock_outerPinchStep_of_uniform (h : ExtremalBlockUniformStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  outerPinchStep_of_block (roseExtremalBlock_of_extremalBlockUniform h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.extremalBlock_targetBlockNoWrap_nil
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.extremalBlock_targetPrefix_of_uniform
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.extremalBlock_clauses_of_uniform
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.ExtremalBlockUniformStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.roseExtremalBlock_of_extremalBlockUniform
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.extremalMinimalUniform_of_extremalBlockUniform
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.extremalBlock_outerPinchStep_of_uniform
