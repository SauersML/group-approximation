import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Contiguity of the extremal region: the residual planarity clauses

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-11a.

`P10ExtremalSplit.RoseExtremalContiguityStatement` asks for a witness of the fifteen clauses
`ExtremalContigClauses`.  One of them, the properness `t₂.length < (outerDarts X).length` of the
new target arc, is elementary: the positional containment
`K.targetArc.start ≤ t₂.start`, `t₂.start + t₂.length ≤ K.targetArc.start + K.targetArc.length`
gives `t₂.length ≤ K.targetArc.length`, and the premise
`K.targetArc.length < (outerDarts X).length` finishes by `omega`.

* `ExtremalContigResidualClauses`: the fourteen remaining clauses.
* `RoseExtremalContigResidualStatement` (OPEN, PLAUSIBLE): some witness of the residual clauses.
  This is strictly smaller in proof content than the contiguity statement (the target properness
  is no longer asked for) and implied by it (it drops a conjunct), so it is true whenever the
  contiguity statement is.
* `contiguity_of_contigResidual` (proved): the residual statement gives the contiguity statement.

## Mathematical route for the residual (not formalised)

Take the extremal pinch region `Z` of the rose configuration: among the regions of the flip move
(`regionColour` classes of `walkKeep K.boundary.cycle`) meeting the kept face and not the
exterior face, one bounded by the fewest boundary darts.  Its boundary walk, read in the cyclic
order of `K.boundary.cycle`, meets the source arc in one block (a sub-arc `t₁` of
`K.sourceArc`, so `source = K.source` and properness of `t₁` comes from the premise
`K.sourceArc.length < (cellDarts X K.source).length`), meets the target arc in one block `t₂`
(positionally inside `K.targetArc`), and its remaining darts come from the two sides, one side
each.  The permutation clause is `c.filter movePred` read off this decomposition; the chain and
junction clauses are the vertex continuity of `K.boundary.cycle` restricted to the blocks.  The
planarity input (Jordan separation of the pinch) is not available from the flip-move API; that is
the remaining gap.

## Truth check

Exhaustive search over rose configurations with at most five petals (scratchpad
`gl-p10-11a/contig_search.py`): 542 configurations, 0 violations of the clauses (strict mode:
one flipped region, contiguous blocks, one side per free side, junctions, non-empty listing).  The
search does not model least area, labels, `Unpinched`, or genuine cell structure.  Reported risk:
a wrapping target arc (`K.targetArc.start + K.targetArc.length > (outerDarts X).length`) whose
extremal region eats a prefix of the arc across the base point, where no `t₂` starts above the old
start; the core bound `lo ≤ t₂.start` carries the same risk.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalContig

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section Clauses

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The residual contiguity clauses**: `P10ExtremalSplit.ExtremalContigClauses` without the
properness `t₂.length < (outerDarts X).length` of the new target arc. -/
def ExtremalContigResidualClauses (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    (source kept : Fin X.rCellCount) (t₁ : CyclicArc (cellDarts X source))
    (t₂ : CyclicArc (outerDarts X)) (s₁ s₂ : List X.toCombMap.Dart) : Prop :=
  (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
    (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
  (cell X source).face ∉ flipFaces X.toCombMap K.faces
    (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
  (cell X kept).face ∈ flipFaces X.toCombMap K.faces
    (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
  List.Perm (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
    (K.boundary.cycle.filter (movePred X.toCombMap
      (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r))) ∧
  s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts ≠ [] ∧
  (s₁.IsChain fun d e =>
    X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
  (s₂.IsChain fun d e =>
    X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
  (∀ a ∈ s₁.getLast?, ∀ b ∈ (invDarts X t₁.darts).head?,
    X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
  (∀ a ∈ (s₁ ++ invDarts X t₁.darts).getLast?, ∀ b ∈ s₂.head?,
    X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
  (∀ a ∈ (s₁ ++ invDarts X t₁.darts ++ s₂).getLast?, ∀ b ∈ t₂.darts.head?,
    X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
  t₁.length < (cellDarts X source).length ∧
  K.targetArc.start.1 ≤ t₂.start.1 ∧
  t₂.start.1 + t₂.length ≤ K.targetArc.start.1 + K.targetArc.length ∧
  (((∀ d ∈ s₁, d ∈ K.firstSide) ∧ (∀ d ∈ s₂, d ∈ K.secondSide)) ∨
    ((∀ d ∈ s₁, d ∈ K.secondSide) ∧ (∀ d ∈ s₂, d ∈ K.firstSide)))

end Clauses

/-- **The residual contiguity statement** (OPEN, PLAUSIBLE; the planarity core of the rose step
without the target properness).  Under the premises of `RoseExtremalCoreStatement`, some witness
satisfies `ExtremalContigResidualClauses`. -/
def RoseExtremalContigResidualStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ (r : X.toCombMap.Dart) (source kept : Fin X.rCellCount)
          (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
          (s₁ s₂ : List X.toCombMap.Dart),
            ExtremalContigResidualClauses K r source kept t₁ t₂ s₁ s₂

/-- **Contiguity from the residual clauses**: the target properness follows from the positional
containment of `t₂` in `K.targetArc` and the premise `K.targetArc.length < (outerDarts X).length`.
-/
theorem contiguity_of_contigResidual
    (h : RoseExtremalContigResidualStatement.{u, w, v}) :
    P10ExtremalSplit.RoseExtremalContiguityStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, source, kept, t₁, t₂, s₁, s₂, hrout, hsource, hkept, hperm, hne, hs₁c, hs₂c,
      hj₁, hj₂, hj₃, ht₁, hlo, hhi, hside⟩ :=
    h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  refine ⟨r, source, kept, t₁, t₂, s₁, s₂, hrout, hsource, hkept, hperm, hne, hs₁c, hs₂c,
    hj₁, hj₂, hj₃, ht₁, ?_, hlo, hhi, hside⟩
  omega

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalContig

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalContig.ExtremalContigResidualClauses
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalContig.RoseExtremalContigResidualStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalContig.contiguity_of_contigResidual
