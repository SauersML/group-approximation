import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-53: the witness step only at pinches off an open lobe

Lane gl-p07-53.  The target is `FourPieceWitness.WitnessStepPinchStatement`
(`WitnessStepPinchStatement.lean`, lane gl-p07-52).  This file states the residual
`FourPieceWitness.WitnessStepPinchOffStatement`.  `WitnessStepPinchOffProof.lean` proves the target
from it (`FourPieceWitness.witnessStepPinch_of_witnessStepPinchOff`).  Certifies no printed
sentence on its own.  NOT COMPILED: this lane was authored without running Lean.

## Notation

`Γ = G₁ · B · G₂ · A` with `B = b.sideFrom i` and `A = a.sideFrom j`, `F = witnessFaces a b K c`
with `c = C.face`, `ow` the enclosing walk of `F`.  A face is **open**
(`IsOpenFace a b K c`) when it lies on the side of `K.walk` and off the cut.

## The lobe of a pinch

At a pinch `(x, y)` (`WitnessStepPinchAt`) the curve `Γ` goes on from `α y` to a dart `g` off
the walk, at the vertex of `y`.  The **lobe face** is `faceOf (α g)`, the face across `g`.  An
**off-lobe pinch** (`WitnessStepPinchOffAt a b K c G₁ G₂ ow x y`) is a pinch whose lobe face:
* is **not open**; and
* **lies in the cut** when `g` is a dart of `G₁` or of `G₂`.

## The residual

Same premise block as the target.  Its forward disjunct is asked only for pairs `(x, y)` with no
cell, side, block-order or corner turn **that form an off-lobe pinch**.  The backward disjunct is
unchanged.

## Route of the reduction (`WitnessStepPinchOffFace.lean`, `WitnessStepPinchOffProof.lean`)

Every pinch is an off-lobe pinch, under the premises.
* `g` is a dart of `Γ`, so `faceOf g` is the cell face of `Π_i` or `Π_j`, or a face of `a` or `b`.
  None of these is in `F`.
* `g ∉ ow` and `faceOf g ∉ F`, so `mem_iff` of the enclosing walk gives `faceOf (α g) ∉ F`.
* `faceOf (α g) = faceOf (σ g)` (as `facePerm (α g) = σ g`), and `σ g` sits at the vertex of `g`,
  which is the vertex of `y` (`witnessStepSkip_vertexOf_of_rotate`).  Also `faceOf y ∈ F`.  So the
  lobe face touches the witness face `faceOf y` at a vertex (`Touch`, second disjunct).  If it
  were open, one more `Step` would put it in `F`.  So it is not open.
* If `g ∈ G₁` or `g ∈ G₂`, then `α g` is a dart of `K.walk` (the arcs `K.firstArc`,
  `K.secondArc` are walked inverted).  So the lobe face is a side face of `K.walk`
  (`mem_sideFaces_iff`), and being not open, it is in the cut.

## Truth check

**TRUE, provided the target is true.**  An off-lobe pinch is a pinch (drop the two new
conjuncts), so the target implies the residual.

Python model (`SP/gl-p07-53/pinch_model.py`, scratchpad, not part of the build): a flower of `k`
petals at one vertex, `k = 1, ..., 5`, all cut masks, every linearisation of the inverted curve.
Every consecutive pair satisfies `StepNext` (forward or wrap-around), so no counter-model.
Pinches occur (600 at `k = 5`), and **only when some petal is cut**.  At every pinch the model
confirmed: `g` is not kept, `faceOf (α g) ∉ F`, `faceOf (σ g) = faceOf (α g)` at the vertex of
`y`, and `faceOf (α g)` is in the cut.  With no cut petal there is no pinch.

The new hypothesis is not vacuous: a cut petal gives a genuine off-lobe pinch.  So the pinch case
is **not** contradictory, and the target is **not** proved outright here.

## LOUD: equal in logical strength, strictly smaller in proof content

Together with the proved reduction, this residual is **logically equivalent** to
`WitnessStepPinchStatement`.  This is forced: any residual that is implied by the target and
suffices for it is equivalent to it.  It is **not** strictly weaker in logic, and it is not
stronger.  It is strictly smaller in proof content: the pinches whose lobe face is open are
discharged.  Among them is the self-pinch at a vertex where the lobe beyond `g` is an open face
reachable from the witness faces.  What is left is the **Jordan-type cyclic-order fact at a pinch
whose lobe is closed**: the lobe face is a cut face or off the side of `K.walk`.
* **Backward disjunct kept**, as in the target.
* **No context-free form.**  A Jordan statement stripped of the pocket premises is FALSE (the
  three-petal model in `P06LakeFree/EnclosedOrder.lean`).  So the premise block is kept whole.
* **AVOID list respected.**  No reduction to `RigidPolarSupportSeparation`,
  `RigidPolarCharacterization`, `KerNormallyGenerated`, `PocketFourPieceLakeReadStatement`,
  `PocketFourPieceWitnessPlanarStatement`, `PocketFourPieceWitnessArcsStatement`,
  `FrameConeFourStatement` or `ExtremalEndBlockStatement`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section PinchOffStatement

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **An off-lobe pinch of the curve at `(x, y)`.**  A pinch (`WitnessStepPinchAt`) at a dart `g`
whose lobe face `faceOf (α g)` is not open, and lies in the cut when `g` is a dart of `G₁` or
`G₂`. -/
def WitnessStepPinchOffAt (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (c : X.toCombMap.Face) (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    (ow : List X.toCombMap.Dart) (x y : X.toCombMap.Dart) : Prop :=
  ∃ g : X.toCombMap.Dart,
    (WitnessStepSkipPieceNext a b G₁ G₂ (X.toCombMap.alpha y) g ∨
      WitnessStepPinchJunctionNext a b G₁ G₂ (X.toCombMap.alpha y) g) ∧
    g ∉ ow ∧ X.toCombMap.vertexOf g = X.toCombMap.vertexOf (X.toCombMap.alpha x) ∧
    ¬ IsOpenFace a b K c (X.toCombMap.faceOf (X.toCombMap.alpha g)) ∧
    (g ∈ G₁.darts ∨ g ∈ G₂.darts → X.toCombMap.faceOf (X.toCombMap.alpha g) ∈ cut a b K c)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepPinchOffAt

end PinchOffStatement

/-- **Residual of lane gl-p07-53: the witness step only at off-lobe pinches of the curve.**  Same
premises as `WitnessStepPinchStatement`.  The forward disjunct is asked only for pairs `(x, y)`
with no cell, side, block-order or corner turn that are also an off-lobe pinch
(`WitnessStepPinchOffAt`).  LOUD: logically equivalent to that statement given the proved
reduction `witnessStepPinch_of_witnessStepPinchOff`, and strictly smaller only in proof content.
See the module docstring. -/
def WitnessStepPinchOffStatement : Prop :=
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
            WitnessStepPinchOffAt a b K C.face G₁ G₂ outerWalk x y →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) x y) ∨
          ∀ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
            (invDarts X outerWalk).rotate n = s ++ x :: y :: t →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) y x

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepPinchOffStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
