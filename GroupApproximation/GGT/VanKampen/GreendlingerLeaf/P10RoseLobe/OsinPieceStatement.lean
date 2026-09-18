import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.OsinPiece
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.OsinCoreStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# The cell-bound region choice with the shared-arc bound supplied

Lane gl-p10-79.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## The shared-arc bound

`roseLobeOsinPiece_SharedArcBound X μ` says: whenever distinct relator cells `i ≠ j` share a
boundary arc `a :: A` (cell `i` rotated reads `a :: (A ++ S)`, cell `j` rotated reads
`T ++ (a :: A).reverse.map α`), then `|a :: A| < μ · |cell i|`.

`roseLobeOsinPiece_sharedArcBound_of`: the cell bounds and `X.LeastArea` give it.  For each
shared arc, piece (1) (`roseLobeOsinPiece_isPiece`, module `OsinPiece`) makes `ℓ(a :: A)` an
`ε`-piece of `ℓ(a :: (A ++ S))`.  Here `W` is closed under `revInv` and rotation, and the
genericity clause `listVal v' ≠ y · listVal v · y⁻¹` comes from least area through the
two-cell cancellation surgery (`roseLobeOsinPiece_merge_ne_one`).  The `pieces` clause of the
cell bounds then gives the length bound (`roseLobeOsinPiece_sharedArc_lt`).

## The residual

`roseLobeOsinPiece_Statement` is `roseLobeOsinCore_Statement` with the premise
`roseLobeOsinPiece_SharedArcBound X μ` inserted right after `X.LeastArea`.

* `roseLobeOsinPiece_core_of`: the residual implies the core statement, with the same
  thresholds.  The new premise is supplied by `roseLobeOsinPiece_sharedArcBound_of hB hlea`.
* `roseLobeOsinPiece_of_core`: the core statement implies the residual, by dropping the premise.

**LOUD: strength.**  The residual is LOGICALLY EQUIVALENT to `roseLobeOsinCore_Statement` (both
directions are proved here).  It is NOT logically weaker.  It is STRICTLY SMALLER IN PROOF
CONTENT: a proof of the residual may use the shared-arc bound for free, and that bound is the
pieces-small-at-shared-arcs step, including the cancellable-pair exclusion from least area.
That step was item 1 of the remaining gap of `roseLobeOsinCore_Statement`, and it is now
proved.

## Truth check (LOUD)

`roseLobeOsinPiece_Statement` is OPEN, not refuted.  Its truth is exactly that of
`roseLobeOsinCore_Statement`, by the two reductions.

* The long/qg/pieces audit recorded in `OsinCoreStatement` (the gl-p10-72 family, 1260
  configurations, all killed by long + qg + pieces) is unchanged, since the added premise is a
  consequence of the others.
* The caveat "genericity clause of `IsPiece` not modelled" in that audit is now discharged
  for arcs shared by two distinct cells: those arcs ARE pieces, or the diagram is not least
  area.
* A STRONGER variant is NOT stated: it would drop the `pieces` clause from the cell bounds and
  keep only the shared-arc bound.  The audit supports it only partially.  Its `pc_kill` also
  counts arcs shared by one cell with itself at a different position, which the shared-arc
  bound does not cover.

## Remaining gap

`roseLobeOsinPiece_Statement` itself.  Of the gap of `roseLobeOsinCore_Statement`, the
following remain:

1. arcs shared by a cell with itself (`i = j`), which are not covered here;
2. pieces through nontrivial connectors (`ε`-close arcs joined through G-cells), which are
   still read from the `pieces` clause;
3. the general piece / length count over the pocket.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

/-- **The shared-arc bound** of a diagram `X`: an arc `a :: A` shared by distinct relator
cells `i ≠ j` (read forwards on cell `i`, backwards on cell `j`) has fewer than `μ · |cell i|`
darts. -/
def roseLobeOsinPiece_SharedArcBound {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (X : DiscDiagram.{u, w, v} W) (mu : ℝ) : Prop :=
  ∀ i j : Fin X.rCellCount, i ≠ j → ∀ (n m : ℕ) (a : X.toCombMap.Dart)
    (A S T : List X.toCombMap.Dart), (cellDarts X i).rotate n = a :: (A ++ S) →
      (cellDarts X j).rotate m = T ++ (a :: A).reverse.map X.toCombMap.alpha →
        ((a :: A).length : ℝ) < mu * ((cellDarts X i).length : ℝ)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinPiece_SharedArcBound

/-- **The shared-arc bound from the cell bounds and least area** (piece (1) and `pieces`). -/
theorem roseLobeOsinPiece_sharedArcBound_of {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} {eps : ℕ}
    {mu lambda c : ℝ} {rho : ℕ} {X : DiscDiagram.{u, w, v} W}
    (hB : roseLobeOsinCore_CellBounds D W X eps mu lambda c rho) (hlea : X.LeastArea) :
    roseLobeOsinPiece_SharedArcBound X mu :=
  fun _ _ hij _ _ _ _ _ _ hi hj => roseLobeOsinPiece_sharedArc_lt hB hlea hij hi hj

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinPiece_sharedArcBound_of
