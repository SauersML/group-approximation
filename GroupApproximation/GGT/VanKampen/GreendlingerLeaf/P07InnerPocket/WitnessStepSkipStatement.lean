import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCornerStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-51: the witness step only at skips of the curve

Lane gl-p07-51.  The target is `FourPieceWitness.WitnessStepCornerResidualStatement`
(`WitnessStepCornerStatement.lean`, lane gl-p07-50).  This file states the residual
`FourPieceWitness.WitnessStepSkipStatement`.  `WitnessStepSkipProof.lean` proves the target from
it (`FourPieceWitness.witnessStepCorner_of_witnessStepSkip`).  Certifies no printed sentence on
its own.  NOT COMPILED: this lane was authored without running Lean.

## Notation

`l = invDarts X outerWalk`, `w = witnessSublistCurve a b G₁ G₂` and `StepNext` are as in the
target.  `Γ` is the closed curve `G₁ · b.sideFrom i · G₂ · a.sideFrom j`, read in its four pieces.
For a pair `(x, y)` consecutive in a rotation of `l`, the walk `outerWalk` has `α y` followed by
`α x`.

## Skips

`WitnessStepSkipPieceNext a b G₁ G₂ d g` says `g` comes right after `d` inside one piece of `Γ`.
A **skip at `(x, y)`** (`WitnessStepSkipAt`) is one of the following.
* **A pinch.**  The next dart `g` after `α y` in its piece is off the walk, but `g` starts at the
  same vertex as the next walk dart `α x`.  So `Γ` passes twice through that vertex.
* **A piece end.**  `α y` is the last dart of `b.sideFrom i`, `G₂` or `a.sideFrom j`.  Formally,
  `α y ∉ G₁.darts` and `α y` has no successor in any piece.

## The residual

Same premise block as the target.  Its forward disjunct is asked only for pairs `(x, y)` with no
cell, side, block-order or corner turn (as in the target) **that also form a skip**.  The backward
disjunct is unchanged, word for word.

## Route of the reduction (`WitnessStepSkipVertex.lean`, `WitnessStepSkipProof.lean`)

Suppose a pair `(x, y)` has no cell turn and no corner turn.  Then it is a skip
(`witnessStepSkip_skipAt`).
* **Piece successors keep the vertex.**  Suppose `g` comes after `d` in a piece.  On a cell arc,
  `g = facePerm d = σ (α d)` (`PocketRun.arcDarts_isChain`).  On a region side, `g = σ^m (α d)`
  (`witnessStepSide_sigma_of_boundaryStep`).  Either way `g` starts where `α d` starts.
* **Walk successors keep the vertex.**  `α x = σ^m y` for the first kept `m`
  (`PocketRun.exists_firstKeep`, `witnessStepSide_sigma_of_rotate`), so `α x` starts at `y`'s
  vertex.
* **Cases.**  Suppose the successor `g` of `α y` is on the walk.  Then it is a turn: a cell turn on
  `G₁`, or a corner turn on `b.sideFrom i`, `G₂` or `a.sideFrom j`.  Suppose `g` is off the walk.
  Then the two points above make it a pinch.  Suppose `α y` has no successor and lies on `G₁`.
  Then it is the last dart of `G₁`, so `y` is the head of `w` and the wrap-around corner turn
  holds.  Otherwise it is a piece end.

## Truth check

**TRUE, provided the target is true.**  The target implies this residual: its forward disjunct
asks for less (one more hypothesis per pair), and its backward disjunct is the target's.  The chain
of targets goes back to `WitnessCurveSublistStepStatement`, which lane gl-p07-32 checked on the
models M11 and M12 with no counter-model (see `FourBlockNondegStepStatement.lean`).

The new hypothesis is not vacuous.  Take a model in which `Γ` touches itself at a vertex `v` and
the walk short-cuts the lobe of `Γ` at `v`.  The pair at `v` is then a pinch.  At the end of
`b.sideFrom i`, the walk continues onto `G₂` and makes a piece end.

## LOUD: equal in logical strength, strictly smaller in proof content

Together with the proved reduction, this residual is **logically equivalent** to
`WitnessStepCornerResidualStatement`.  It is **not** strictly weaker in logic.  Any residual
sufficient for the target is at least as strong, so no weaker one exists.  It is strictly
smaller in proof content: every pair at a vertex where `Γ` does not touch itself is now discharged,
except at the three piece ends.  In the target that case, "the successor of `α y` on `Γ` is off
the walk", had to be excluded by hand.  Here it is refuted by the vertex bookkeeping above.  The
last dart of `G₁` is discharged too.

What is left is the **Jordan-type cyclic-order fact alone**: at a pinch of `Γ` or at a piece end,
the walk resumes `Γ` further along in its cyclic order (`StepNext`), never behind.  The piece-end
case also needs the junctions of `Γ` (`b.sideFrom i` ends where `G₂` starts, and so on), which the
repository does not state.

* **Backward disjunct kept.**  Discharging it would need a forward-only statement.  That is
  logically stronger than the target, and its truth is unchecked.  We do not assert it.
* **No context-free form.**  A Jordan statement stripped of the pocket premises is FALSE.  See
  the three-petal model in `P06LakeFree/EnclosedOrder.lean`.  So the premise block is kept whole.
* **AVOID list respected.**  No reduction to `PocketFourPieceLakeReadStatement`,
  `PocketFourPieceWitnessPlanarStatement` or `PocketFourPieceWitnessArcsStatement`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section SkipStatement

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **`g` comes right after `d` in one piece of the curve.**  The pieces are `G₁`,
`b.sideFrom i`, `G₂` and `a.sideFrom j`. -/
def WitnessStepSkipPieceNext (a b : RegionCandidate D eps X) (G₁ : CyclicArc (cellDarts X i))
    (G₂ : CyclicArc (cellDarts X j)) (d g : X.toCombMap.Dart) : Prop :=
  (∃ p q : List X.toCombMap.Dart, G₁.darts = p ++ d :: g :: q) ∨
    (∃ p q : List X.toCombMap.Dart, b.sideFrom i = p ++ d :: g :: q) ∨
    (∃ p q : List X.toCombMap.Dart, G₂.darts = p ++ d :: g :: q) ∨
    ∃ p q : List X.toCombMap.Dart, a.sideFrom j = p ++ d :: g :: q

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepSkipPieceNext

/-- **A skip of the curve at `(x, y)`.**  Either it is a pinch, or `α y` ends a piece other than
`G₁`.  At a pinch, the piece successor `g` of `α y` is off the walk `ow`, but starts at the vertex
of the next walk dart `α x`. -/
def WitnessStepSkipAt (a b : RegionCandidate D eps X) (G₁ : CyclicArc (cellDarts X i))
    (G₂ : CyclicArc (cellDarts X j)) (ow : List X.toCombMap.Dart) (x y : X.toCombMap.Dart) :
    Prop :=
  (∃ g : X.toCombMap.Dart, WitnessStepSkipPieceNext a b G₁ G₂ (X.toCombMap.alpha y) g ∧
      g ∉ ow ∧ X.toCombMap.vertexOf g = X.toCombMap.vertexOf (X.toCombMap.alpha x)) ∨
    (X.toCombMap.alpha y ∉ G₁.darts ∧
      ∀ g : X.toCombMap.Dart, ¬ WitnessStepSkipPieceNext a b G₁ G₂ (X.toCombMap.alpha y) g)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepSkipAt

end SkipStatement

/-- **Residual of lane gl-p07-51: the witness step only at skips of the curve.**  Same premises
as `WitnessStepCornerResidualStatement`.  The forward disjunct is asked only for pairs `(x, y)`
with no cell, side, block-order or corner turn that are also a skip (`WitnessStepSkipAt`).  LOUD:
logically equivalent to that statement given the proved reduction
`witnessStepCorner_of_witnessStepSkip`, and strictly smaller only in proof content.  See the
module docstring. -/
def WitnessStepSkipStatement : Prop :=
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
            WitnessStepSkipAt a b G₁ G₂ outerWalk x y →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) x y) ∨
          ∀ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
            (invDarts X outerWalk).rotate n = s ++ x :: y :: t →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) y x

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepSkipStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
