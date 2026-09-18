import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSkipStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-52: the witness step only at pinches of the curve

Lane gl-p07-52.  The target is `FourPieceWitness.WitnessStepSkipStatement`
(`WitnessStepSkipStatement.lean`, lane gl-p07-51).  This file states the residual
`FourPieceWitness.WitnessStepPinchStatement`.  `WitnessStepPinchProof.lean` proves the target from
it (`FourPieceWitness.witnessStepSkip_of_witnessStepPinch`).  Certifies no printed sentence on its
own.  NOT COMPILED: this lane was authored without running Lean.

## The junctions of `Γ = G₁ · B · G₂ · A`

Write `B = b.sideFrom i` and `A = a.sideFrom j`.  `WitnessStepPinchJunctionNext a b G₁ G₂ d g`
says that `d` is the last dart of a piece of `Γ` and `g` is the first dart of the next nonempty
piece, read cyclically but stopping at `G₁` (the start of `w`):
* `d` ends `B`, and `g` starts `G₂`; or `G₂ = []` and `g` starts `A`; or `G₂ = A = []` and `g`
  starts `G₁`;
* `d` ends `G₂`, and `g` starts `A`; or `A = []` and `g` starts `G₁`;
* `d` ends `A`, and `g` starts `G₁`.

The **junction facts** (`WitnessStepPinchJunction.lean`) say that in each of these six cases `g`
is reached from `α d` by a σ-fan: `g = σ^m (α d)` with `m ≥ 1`, and each dart `σ^k (α d)` with
`0 < k < m` has both of its faces off the enclosed face set `F`.  They are TRUE as formalized and
proved from the data: the region boundary cycles
(`RegionCandidate.boundary_cycle_rotate_of_joinsCells`), the cell arc chains
(`PocketRun.arcDarts_isChain`) and the decompositions `K.firstArc = a_i · G₁ · b_i`,
`K.secondArc = b_j · G₂ · a_j`.  None of the junction facts stated here is false.

## Pinches

A **pinch at `(x, y)`** (`WitnessStepPinchAt`) is a dart `g` that follows `α y` on `Γ`, either
inside a piece (`WitnessStepSkipPieceNext`) or across a junction (`WitnessStepPinchJunctionNext`),
with `g` off the walk but at the vertex of the next walk dart `α x`.

## The residual

Same premise block as the target.  Its forward disjunct is asked only for pairs `(x, y)` with no
cell, side, block-order or corner turn **that form a pinch**.  The backward disjunct is unchanged.

## Route of the reduction (`WitnessStepPinchEnd.lean`, `WitnessStepPinchProof.lean`)

A skip is either a pinch inside a piece (already a pinch here), or a piece end: `α y` is the last
dart `d` of `B`, `G₂` or `A`.  At a piece end, either `y` heads `w` (all later pieces up to `G₁`
are empty), and the wrap-around disjunct of `StepNext` holds.  Or a junction gives the next dart
`g` with a σ-fan from `α d`.  The fan's inner darts are not walk edges, since their faces are off
`F`.  So if `g` is on the walk, it is the first kept dart, and `g = α x`.  Then `x = α g` lies in an
earlier block of `w` than `y`, and the forward disjunct holds.  If `g` is off the walk, the fan and
the walk successor both keep the vertex of `y`, so the pair is a pinch across a junction.

## Truth check

**TRUE, provided the target is true.**  The target's forward disjunct gives the step for every
pair with no turns and a skip.  A pinch across a junction need not be a skip, but the target of
lane gl-p07-51 (`WitnessStepCornerResidualStatement`) gives the step with no skip hypothesis, and
it implies this residual directly.  The chain of targets goes back to
`WitnessCurveSublistStepStatement`, checked by lane gl-p07-32 on the models M11 and M12.

## LOUD: equal in logical strength, strictly smaller in proof content

Together with the proved reductions, this residual is **logically equivalent** to
`WitnessStepSkipStatement` and to `WitnessStepCornerResidualStatement`.  It is **not** strictly
weaker in logic, and it is not stronger.  It is strictly smaller in proof content: the piece-end
case of `WitnessStepSkipAt` is now discharged, except when the junction dart is off the walk.
What is left is the **Jordan-type cyclic-order fact at a pinch alone**, inside a piece or across a
junction.  The walk leaves `Γ` at a vertex that `Γ` visits twice and must come back to `Γ` further
along, never behind.
* **Backward disjunct kept**, as in the target.
* **No context-free form.**  A Jordan statement stripped of the pocket premises is FALSE (the
  three-petal model in `P06LakeFree/EnclosedOrder.lean`).  So the premise block is kept whole.
* **AVOID list respected.**  No reduction to `PocketFourPieceLakeReadStatement`,
  `PocketFourPieceWitnessPlanarStatement` or `PocketFourPieceWitnessArcsStatement`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section PinchStatement

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **`g` follows `d` across a junction of the curve.**  `d` is the last dart of `b.sideFrom i`,
`G₂` or `a.sideFrom j`, and `g` is the first dart of the next nonempty piece, stopping at `G₁`. -/
def WitnessStepPinchJunctionNext (a b : RegionCandidate D eps X) (G₁ : CyclicArc (cellDarts X i))
    (G₂ : CyclicArc (cellDarts X j)) (d g : X.toCombMap.Dart) : Prop :=
  ((∃ p : List X.toCombMap.Dart, b.sideFrom i = p ++ [d]) ∧
      ((∃ q : List X.toCombMap.Dart, G₂.darts = g :: q) ∨
        (G₂.darts = [] ∧ ((∃ q : List X.toCombMap.Dart, a.sideFrom j = g :: q) ∨
          (a.sideFrom j = [] ∧ ∃ q : List X.toCombMap.Dart, G₁.darts = g :: q))))) ∨
    ((∃ p : List X.toCombMap.Dart, G₂.darts = p ++ [d]) ∧
      ((∃ q : List X.toCombMap.Dart, a.sideFrom j = g :: q) ∨
        (a.sideFrom j = [] ∧ ∃ q : List X.toCombMap.Dart, G₁.darts = g :: q))) ∨
    ((∃ p : List X.toCombMap.Dart, a.sideFrom j = p ++ [d]) ∧
      ∃ q : List X.toCombMap.Dart, G₁.darts = g :: q)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepPinchJunctionNext

/-- **A pinch of the curve at `(x, y)`.**  A dart `g` follows `α y` on the curve, inside a piece
or across a junction.  It is off the walk `ow`, but starts at the vertex of the next walk dart
`α x`. -/
def WitnessStepPinchAt (a b : RegionCandidate D eps X) (G₁ : CyclicArc (cellDarts X i))
    (G₂ : CyclicArc (cellDarts X j)) (ow : List X.toCombMap.Dart) (x y : X.toCombMap.Dart) :
    Prop :=
  ∃ g : X.toCombMap.Dart,
    (WitnessStepSkipPieceNext a b G₁ G₂ (X.toCombMap.alpha y) g ∨
      WitnessStepPinchJunctionNext a b G₁ G₂ (X.toCombMap.alpha y) g) ∧
    g ∉ ow ∧ X.toCombMap.vertexOf g = X.toCombMap.vertexOf (X.toCombMap.alpha x)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepPinchAt

end PinchStatement

/-- **Residual of lane gl-p07-52: the witness step only at pinches of the curve.**  Same premises
as `WitnessStepSkipStatement`.  The forward disjunct is asked only for pairs `(x, y)` with no
cell, side, block-order or corner turn that are also a pinch (`WitnessStepPinchAt`).  LOUD:
logically equivalent to that statement given the proved reduction
`witnessStepSkip_of_witnessStepPinch`, and strictly smaller only in proof content.  See the module
docstring. -/
def WitnessStepPinchStatement : Prop :=
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
            WitnessStepPinchAt a b G₁ G₂ outerWalk x y →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) x y) ∨
          ∀ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
            (invDarts X outerWalk).rotate n = s ++ x :: y :: t →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) y x

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepPinchStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
