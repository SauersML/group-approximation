import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSideStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-49: the witness step residual off block-order turns

Lane gl-p07-49.  The target is `FourPieceWitness.WitnessStepSideResidualStatement`
(`WitnessStepSideStatement.lean`, lane gl-p07-47).  This file states the residual
`FourPieceWitness.WitnessStepBlockResidualStatement`.  `WitnessStepBlockProof.lean` proves the
target from it (`FourPieceWitness.witnessStepSideResidual_of_witnessStepBlock`).  Certifies no
printed sentence on its own.

## Notation

* `l = invDarts X outerWalk`, `w = witnessSublistCurve a b G₁ G₂ = Ḡ₁ · Ā · Ḡ₂' · B̄`,
  `StepNext` as in the target.
* A **block-order turn** `(x, y)` (`WitnessStepBlockTurn`) is a pair in which `x` lies in a block
  of `w` strictly before a block that contains `y`:
  * `x ∈ Ḡ₁` and `y ∉ Ḡ₁` (then `y` lies in a later block, since `y ∈ l ⊆ w`);
  * `x ∈ Ā` and `y ∈ Ḡ₂' ∪ B̄`;
  * `x ∈ Ḡ₂'` and `y ∈ B̄`.

## The residual

Same premise block as the target.  Conclusion: the forward disjunct is asked only for pairs
`(x, y)` with no cell turn at `y`, no side turn at `y`, **and no block-order turn `(x, y)`**.  The
backward disjunct is unchanged.

## Route of the reduction (`WitnessStepBlockStep.lean`)

`StepNext w l x y` in its forward form only asks that `x` come before `y` in `w`; it does not ask
that they be adjacent.  In a block-order turn, `x` is in an earlier block than `y`, so this holds
by `witnessStep_forward_of_mem_append`.  In the first case, `y ∈ w` comes from the step 1 label
`hlab` (`witnessSublist_mem_curve`).

## Truth check

**TRUE, provided the target is true.**  The target implies the residual: the forward disjunct
asks for less, with one more hypothesis per pair, and the backward disjunct is the target's.  The
chain of targets goes back to `WitnessCurveSublistStepStatement`, which lane gl-p07-32 checked on
the models M11 and M12 with no counter-model (see `FourBlockNondegStepStatement.lean`).

The new exclusion is not vacuous.  In a model where the walk runs `w` forward, the three block
changes `Ḡ₁ → Ā`, `Ā → Ḡ₂'`, `Ḡ₂' → B̄` are exactly block-order turns.

## LOUD: equal in logical strength, strictly smaller in proof content

Together with the proved reduction, this residual is **logically equivalent** to
`WitnessStepSideResidualStatement`.  It is **not** strictly weaker in logic.  It is strictly
smaller in proof content: every forward step of the walk from one block of `w` into a later block
is discharged here.  The discharge is **pure list reasoning**; it uses no planar geometry, and in
particular it does not identify the dart that follows the last dart of a side or arc.

What is left, in the forward disjunct, are the pairs with `x` and `y` in the same block and no
cell or side turn at `y`, and the pairs with `y` in a strictly earlier block than `x`.  Since `w`
is duplicate free, a pair of the second kind can satisfy `StepNext w l x y` only through its
second disjunct: `y` must be the first entry of `w` in `l`, i.e. the one wrap-around step.  Also
left, unchanged:
* filtered side turns (on `b.sideFrom i` with `y ∈ Ḡ₁ ∪ Ḡ₂`; on `a.sideFrom j` with `y ∉ Ā`,
  `α g ∈ Ḡ₂` or `g ∈ b.sideFrom i`) when they stay inside one block or go backwards;
* turns along `G₂` into `Ḡ₁`;
* the backward orientation.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section BlockStatement

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A block-order turn `(x, y)`.**  The dart `x` lies in a block of the curve
`Ḡ₁ · Ā · Ḡ₂' · B̄` strictly before a block that contains `y`: `x ∈ Ḡ₁` and `y ∉ Ḡ₁`; or
`x ∈ Ā` and `y ∈ Ḡ₂' ∪ B̄`; or `x ∈ Ḡ₂'` and `y ∈ B̄`. -/
def WitnessStepBlockTurn (a b : RegionCandidate D eps X) (G₁ : CyclicArc (cellDarts X i))
    (G₂ : CyclicArc (cellDarts X j)) (x y : X.toCombMap.Dart) : Prop :=
  (x ∈ invDarts X G₁.darts ∧ y ∉ invDarts X G₁.darts) ∨
    (x ∈ FourBlock.sideAWord a b G₁ G₂ ∧
      (y ∈ FourBlock.cellG2Word G₁ G₂ ∨ y ∈ FourBlock.sideBWord b G₁ G₂)) ∨
    (x ∈ FourBlock.cellG2Word G₁ G₂ ∧ y ∈ FourBlock.sideBWord b G₁ G₂)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepBlockTurn

end BlockStatement
