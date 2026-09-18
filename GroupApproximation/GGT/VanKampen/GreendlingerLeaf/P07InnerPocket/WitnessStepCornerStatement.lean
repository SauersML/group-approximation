import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBlockStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-50: the witness step residual off corner turns

Lane gl-p07-50.  The target is `FourPieceWitness.WitnessStepBlockResidualStatement`
(`WitnessStepBlockStatement.lean`, lane gl-p07-49).  This file states the residual
`FourPieceWitness.WitnessStepCornerResidualStatement`.  `WitnessStepCornerProof.lean` proves the
target from it (`FourPieceWitness.witnessStepBlockResidual_of_witnessStepCorner`).  Certifies no
printed sentence on its own.

## Notation

`l = invDarts X outerWalk`, `w = witnessSublistCurve a b G₁ G₂ = Ḡ₁ · Ā · Ḡ₂' · B̄` and
`StepNext` are as in the target.

## Corner turns

A **corner turn at `y`** (`WitnessStepCornerTurn`) is one of the following.
* An unfiltered side turn along `b.sideFrom i`: a dart `g ∈ outerWalk` right after `α y` on it.
* An unfiltered side turn along `a.sideFrom j`: a dart `g ∈ outerWalk` right after `α y` on it.
* An unfiltered cell turn along `G₂`: a dart `g ∈ outerWalk` right after `α y` on `G₂`.
* The wrap-around: `y` is the first entry of `w` that lies in `l`.

The side and cell turns of the lanes before this one (`WitnessStepSideTurn`, the second disjunct
of `WitnessStepCellTurn`) carry extra filter hypotheses: `y ∈ B̄`, `y ∈ Ā`, `α g ∉ Ḡ₂`,
`g ∉ b.sideFrom i`, and `y ∉ Ḡ₁`.  This lane drops all of them.  They hold at every corner, where a
region side meets `Π_i` or `Π_j`.  The name refers to those corners.

## The residual

Same premise block as the target.  Conclusion: the forward disjunct is asked only for pairs
`(x, y)` with no cell, side or block-order turn (as in the target) **and no corner turn at `y`**.
The backward disjunct is unchanged.

## Route of the reduction (`WitnessStepCornerFace.lean`, `WitnessStepCornerStep.lean`)

The filters are no-ops under the premises.
* **Cells off regions.**  Each of `a`, `b` has a nonempty arc on `Π_i` and on `Π_j`.  An arc dart
  `d` has `α d` on the boundary cycle of the region, so `faceOf d`, the cell face, is not a face of
  the region (`witnessStepCorner_cell_face_not_mem`).
* **Sides off cells.**  A side dart lies on the boundary cycle of its region, so its face is in
  the region.  So it is not a dart of `Π_i` or `Π_j`.  Hence `α y ∈ side` forces `y ∉ Ḡ₁, Ḡ₂`.
* **Sides apart.**  `Disjoint a.1 b.1`, so no dart lies on a side of `a` and on a side of `b`.
  This gives `α y ∉ b.sideFrom i` and `g ∉ b.sideFrom i` for the side `a.sideFrom j`.
* **Cells apart.**  `i ≠ j`, so the faces of `Π_i` and `Π_j` differ (`cell_face_injective`).  A
  dart of `G₂` is not a dart of `G₁`, so `α y ∈ G₂` forces `y ∉ Ḡ₁`.
The filtered turn lemmas `witnessStepSide_step_of_turnB`, `witnessStepSide_step_of_turnA` and
`witnessStep_step_of_cellTurn₂` then give the step.  The wrap-around is the second disjunct of
`StepNext`, word for word.

## Truth check

**TRUE, provided the target is true.**  The target implies the residual.  Its forward disjunct
asks for less, with one more hypothesis per pair, and its backward disjunct is the target's.  The
chain of targets goes back to `WitnessCurveSublistStepStatement`, which lane gl-p07-32 checked on
the models M11 and M12 with no counter-model (see `FourBlockNondegStepStatement.lean`).

The new exclusion is not vacuous.  A walk that runs a region side forward makes a side turn at
every inner dart of that side.  In a model where the walk runs `w` forward and closes up at the
head of `w`, the closing pair is a wrap-around turn.

## LOUD: equal in logical strength, strictly smaller in proof content

Together with the proved reduction, this residual is **logically equivalent** to
`WitnessStepBlockResidualStatement`.  It is **not** strictly weaker in logic.  It is strictly
smaller in proof content.  Every forward pair of these kinds is now discharged:
* filtered side turns, inside one block or backwards;
* turns along `G₂` into `Ḡ₁`, which are impossible;
* the one wrap-around step.
These discharges use planar data: arc and side darts on the region boundary, disjoint regions and
distinct cells.

What is left, in the forward disjunct, are the pairs `(x, y)` where the walk leaves the curve
`Γ = G₁ · b.sideFrom i · G₂ · a.sideFrom j` at `α y` and resumes it at `α x` somewhere else.  That
happens at a pinch vertex, where the next dart after `α y` on `Γ` is not on the walk.  Such a pair
has `x`, `y` in one block or `y` in an earlier block, and no turn at `y`.  The backward orientation
is also left, unchanged.  Closing these needs a Jordan-type statement: the walk meets `Γ` in its
cyclic order.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section CornerStatement

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A corner turn at `y`.**  A dart `g ∈ ow` right after `α y` on `b.sideFrom i`, on
`a.sideFrom j` or on `G₂`, with no filter hypothesis.  Or the wrap-around: `y` is the first entry
of the curve `witnessSublistCurve a b G₁ G₂` that lies in `invDarts X ow`. -/
def WitnessStepCornerTurn (a b : RegionCandidate D eps X) (G₁ : CyclicArc (cellDarts X i))
    (G₂ : CyclicArc (cellDarts X j)) (ow : List X.toCombMap.Dart) (y : X.toCombMap.Dart) :
    Prop :=
  (∃ p q : List X.toCombMap.Dart, ∃ g ∈ ow,
      b.sideFrom i = p ++ X.toCombMap.alpha y :: g :: q) ∨
    (∃ p q : List X.toCombMap.Dart, ∃ g ∈ ow,
      a.sideFrom j = p ++ X.toCombMap.alpha y :: g :: q) ∨
    (∃ p q : List X.toCombMap.Dart, ∃ g ∈ ow,
      G₂.darts = p ++ X.toCombMap.alpha y :: g :: q) ∨
    ∃ u z : List X.toCombMap.Dart, witnessSublistCurve a b G₁ G₂ = u ++ y :: z ∧
      ∀ t ∈ u, t ∉ invDarts X ow

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepCornerTurn

end CornerStatement

/-- **Residual of lane gl-p07-50: the witness step off cell, side, block-order and corner
turns.**  Same premises as `WitnessStepBlockResidualStatement`.  The forward disjunct is asked
only for pairs `(x, y)` with no cell, side, block-order turn and no corner turn at `y`.  LOUD:
logically equivalent to that statement given the proved reduction
`witnessStepBlockResidual_of_witnessStepCorner`, and strictly smaller only in proof content.  See
the module docstring. -/
def WitnessStepCornerResidualStatement : Prop :=
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
            ¬ WitnessStepBlockTurn a b G₁ G₂ x y →
            ¬ WitnessStepCornerTurn a b G₁ G₂ outerWalk y →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) x y) ∨
          ∀ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
            (invDarts X outerWalk).rotate n = s ++ x :: y :: t →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) y x

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepCornerResidualStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
