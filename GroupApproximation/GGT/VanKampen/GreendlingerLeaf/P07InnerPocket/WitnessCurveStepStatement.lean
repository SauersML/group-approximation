import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-40: the witness step residual off the cell turns

Lane gl-p07-40.  The target is `FourPieceWitness.WitnessCurveSublistStepStatement`
(`WitnessCurveSublistStatement.lean`, lane gl-p07-36c).  This file states the residual
`FourPieceWitness.WitnessStepResidualStatement`.  `WitnessCurveStepProof.lean` proves the target
from it (`FourPieceWitness.witnessCurveSublistStep_of_witnessStepResidual`).  Certifies no printed
sentence on its own.

## Notation

* `l = invDarts X outerWalk`, `w = witnessSublistCurve a b G₁ G₂`, `StepNext` as in the target.
* A **cell turn at `y`** (`WitnessStepCellTurn`): a dart `g` of `outerWalk` that immediately
  follows `α y` on `G₁.darts`, or on `G₂.darts` with `y ∉ Ḡ₁`.

## The residual

Same premise block as the target.  Conclusion: the target's forward disjunct is asked only for
the consecutive pairs `(x, y)` with no cell turn at `y`.  The backward disjunct is unchanged.

## Route of the reduction (`WitnessCurveStepCell.lean`)

Let `(x, y)` be consecutive in a rotation of `l`.  Then `(α y, α x)` is consecutive in a
rotation of `outerWalk`.  Say `g ∈ outerWalk` follows `α y` on a cell arc.  The arc is a face
chain, so `facePerm (α y) = g`, and `g` is an edge of the walk.  The walk turns to the first kept
dart (`EnclosedFaceSetSucc.turn_next` with `m = 1`), so `α x = g`.  So `(x, y)` is consecutive in
`Ḡ₁` (resp. `Ḡ₂`).  In `Ḡ₁`, the first block of `w`, this is a forward step.  In `Ḡ₂` with
`y ∉ Ḡ₁`: either `x ∈ Ḡ₁` lies in the first block and `y` in a later one, or both pass the
filter of `cellG2Word` and stay consecutive there.

## Truth check

**TRUE, provided the target is true.**  The target implies the residual: the residual's forward
disjunct asks for less, with one more hypothesis per pair, and its backward disjunct is the
target's.  Lane gl-p07-32 checked the target on the models M11 and M12 and found no counter-model
(see `FourBlockNondegStepStatement.lean`).  The orientation of the cell turns was checked on
paper.  The walk runs the cell arcs forward, since `turn_next` with `m = 1` gives
`ow[k+1] = facePerm ow[k]`.  So a cell turn gives `x` immediately before `y` in `Ḡ₁`, which is
the forward disjunct, not the backward one.

## LOUD: equal in logical strength, strictly smaller in proof content

Together with the proved reduction, the residual is **logically equivalent** to the target.  It
is not strictly weaker in logic.  It is strictly smaller in proof content: every step that
follows a cell arc is discharged here, for both cells.  What is left is the planar case analysis
for the other turns: turns along a region side, turns between blocks, and the one wrap-around
step to the first entry of `w`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section StepStatement

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A cell turn at `y`.**  Some dart `g` of the walk `ow` follows `α y` on `G₁.darts`, or on
`G₂.darts` with `y ∉ Ḡ₁`. -/
def WitnessStepCellTurn (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    (ow : List X.toCombMap.Dart) (y : X.toCombMap.Dart) : Prop :=
  (∃ p q : List X.toCombMap.Dart, ∃ g ∈ ow, G₁.darts = p ++ X.toCombMap.alpha y :: g :: q) ∨
    ∃ p q : List X.toCombMap.Dart, ∃ g ∈ ow,
      G₂.darts = p ++ X.toCombMap.alpha y :: g :: q ∧ y ∉ invDarts X G₁.darts

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepCellTurn

end StepStatement

/-- **Residual of lane gl-p07-40: the witness step off the cell turns.**  Same premises as
`WitnessCurveSublistStepStatement`.  The forward disjunct is asked only for pairs `(x, y)` with no
cell turn at `y`.  LOUD: logically equivalent to that target given the proved reduction
`witnessCurveSublistStep_of_witnessStepResidual`, and strictly smaller only in proof content.  See
the module docstring. -/
def WitnessStepResidualStatement : Prop :=
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
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) x y) ∨
          ∀ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
            (invDarts X outerWalk).rotate n = s ++ x :: y :: t →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) y x

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepResidualStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
