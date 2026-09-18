import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveStepStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-47: the witness step residual off cell and side turns

Lane gl-p07-47.  The target is `FourPieceWitness.WitnessStepResidualStatement`
(`WitnessCurveStepStatement.lean`, lane gl-p07-40).  This file states the residual
`FourPieceWitness.WitnessStepSideResidualStatement`.  `WitnessStepSideProof.lean` proves the target
from it (`FourPieceWitness.witnessStepResidual_of_witnessStepSide`).  Certifies no printed
sentence on its own.

## Notation

* `l = invDarts X outerWalk`, `w = witnessSublistCurve a b G₁ G₂`, `StepNext` as in the target.
* A **side turn at `y`** (`WitnessStepSideTurn`) is a dart `g` of `outerWalk` that immediately
  follows `α y` on one of these sides:
  * on `b.sideFrom i`, with `y ∈ B̄` (the block `sideBWord`);
  * on `a.sideFrom j`, with `y ∈ Ā` (the block `sideAWord`), `α g ∉ Ḡ₂` and
    `g ∉ b.sideFrom i`.

## The residual

Same premise block as the target.  Conclusion: the forward disjunct is asked only for pairs
`(x, y)` with no cell turn **and no side turn** at `y`.  The backward disjunct is unchanged.

## Route of the reduction (`WitnessStepSideWalk.lean`, `WitnessStepSideStep.lean`)

Let `(x, y)` be consecutive in a rotation of `l`, so `(α y, α x)` is consecutive in a rotation of
`outerWalk`.  Suppose `g ∈ outerWalk` follows `α y` on a side of the region `c`.  The side is an
infix of the boundary cycle of `c`, which is a `BoundaryStep` chain.  So `g = σ^m (α (α y))` for
some `m ≥ 1`, and every `σ^k (α (α y))` with `0 < k < m` has both faces in `c.1`.  The witness faces
avoid `c.1` (`not_mem_left_of_mem_witnessFaces` for `a`, `not_mem_right_of_mem_witnessFaces` for
`b`).  Every walk dart looks into the witness (`hnb`), so none of those intermediate darts is an
edge of the walk.  So `g` is the first kept dart, and `turn_next` gives `α x = g`.  Then `(x, y)`
is consecutive in the inverse side.  From there:

* in `B̄`: either both pass the filter, or `x` lies in an earlier block (by the step 1 label);
* in `Ā`: either `x ∈ Ḡ₁` (the first block), or `x` passes the filter by `α g ∉ Ḡ₂` and
  `g ∉ b.sideFrom i`.

## Truth check

**TRUE, provided the target is true.**  The target implies the residual.  Its forward disjunct
asks for less, with one more hypothesis per pair, and its backward disjunct is the target's.  The
target is itself implied by `WitnessCurveSublistStepStatement`, since it asks for less.  Lane
gl-p07-32 checked that statement on the models M11 and M12 and found no counter-model (see
`FourBlockNondegStepStatement.lean`).

Orientation, checked on paper: `BoundaryStep` and `turn_next` both advance by the same rotation
`σ` after crossing (`σ ∘ α = facePerm`).  So the walk runs each region side forward in the order
of the region's boundary cycle.  A side turn gives `x` immediately before `y` in the inverse side,
which is the forward disjunct.  This is consistent with M12, where the witness `P₀` reads
`G₁b · B̄ · Ḡ₂ · Ā`, each side block in its own order.  So the new exclusion is not vacuous in the
models.

## LOUD: equal in logical strength, strictly smaller in proof content

Together with the proved reduction, this residual is **logically equivalent** to
`WitnessStepResidualStatement`.  It is not strictly weaker in logic.  It is strictly smaller in
proof content: every forward step that follows a region side inside a kept block is discharged
here.  What is left:

* turns between blocks, where `α y` is the last dart of a side or arc, or `y` falls in another
  block;
* side turns where the filter drops an entry: on `b.sideFrom i` with `y ∈ Ḡ₁ ∪ Ḡ₂`; on
  `a.sideFrom j` with `y ∉ Ā`, `α g ∈ Ḡ₂` or `g ∈ b.sideFrom i`;
* turns along `G₂` into `Ḡ₁`;
* the one wrap-around step to the first entry of `w`;
* the backward orientation.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section SideStatement

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A side turn at `y`.**  Some dart `g` of the walk `ow` follows `α y` on `b.sideFrom i`, with
`y ∈ B̄`.  Or it follows `α y` on `a.sideFrom j`, with `y ∈ Ā`, `α g ∉ Ḡ₂` and
`g ∉ b.sideFrom i`. -/
def WitnessStepSideTurn (a b : RegionCandidate D eps X) (G₁ : CyclicArc (cellDarts X i))
    (G₂ : CyclicArc (cellDarts X j)) (ow : List X.toCombMap.Dart) (y : X.toCombMap.Dart) :
    Prop :=
  (∃ p q : List X.toCombMap.Dart, ∃ g ∈ ow,
      b.sideFrom i = p ++ X.toCombMap.alpha y :: g :: q ∧ y ∈ FourBlock.sideBWord b G₁ G₂) ∨
    ∃ p q : List X.toCombMap.Dart, ∃ g ∈ ow,
      a.sideFrom j = p ++ X.toCombMap.alpha y :: g :: q ∧ y ∈ FourBlock.sideAWord a b G₁ G₂ ∧
        X.toCombMap.alpha g ∉ invDarts X G₂.darts ∧ g ∉ b.sideFrom i

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepSideTurn

end SideStatement

/-- **Residual of lane gl-p07-47: the witness step off the cell and side turns.**  Same premises
as `WitnessStepResidualStatement`.  The forward disjunct is asked only for pairs `(x, y)` with no
cell turn and no side turn at `y`.  LOUD: logically equivalent to that statement given the proved
reduction `witnessStepResidual_of_witnessStepSide`, and strictly smaller only in proof content.
See the module docstring. -/
def WitnessStepSideResidualStatement : Prop :=
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
        (∀ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
            (invDarts X outerWalk).rotate n = s ++ x :: y :: t →
            ¬ WitnessStepCellTurn G₁ G₂ outerWalk y →
            ¬ WitnessStepSideTurn a b G₁ G₂ outerWalk y →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) x y) ∨
          ∀ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
            (invDarts X outerWalk).rotate n = s ++ x :: y :: t →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) y x

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepSideResidualStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
