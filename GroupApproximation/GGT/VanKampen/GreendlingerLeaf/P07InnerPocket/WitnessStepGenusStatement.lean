import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepWindingStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepGenusFirstReturn
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-60: the winding residual minus its genus argument

Lane gl-p07-60.  States the residual `FourPieceWitness.WitnessStepGenusBridgeStatement`.
Certifies no printed sentence on its own.  NOT COMPILED: authored without running Lean.

## The residual

Write `w = witnessSublistCurve a b G₁ G₂` and `l = invDarts X outerWalk`.  The premise block is
that of `WitnessStepWindingPinchedStatement` (lane gl-p07-59), pinch hypothesis included.  The
residual asks for a **planar model of the curve**: a planar map `N`, a dart map `ι` into `X`, a
list `l'` with `l'.map ι = l`, and a face cycle `Γ` of `N`, such that
* every cyclic step of `l'` is a successor step of `N` (`WitnessStepGenusSucc`);
* every entry of `l'` lies on `Γ`;
* on entries of `l'`, the order of `w` is the order of `Γ` (`WitnessStepGenusBefore`).

## Why it is smaller in proof content (LOUD)

`WitnessStepGenusProof.lean` derives `WitnessStepWindingPinchedStatement` from it.  The genus-zero
argument is proved there (`witnessStepGenus_between_not_mem`, via the Euler characteristic of a
vertex split: `WitnessStepGenusSplit.lean`).  So is the transfer of the first-return property to
`StepNext`.  `SP/gl-p07-59/random_maps.py` shows this genus-zero input is essential: the bound
fails in 948 of 81895 random cases, all of genus > 0.  What is left here is **only the construction
of the planar model**.  There is no counting, no winding and no genus argument.
* It is **not claimed strictly weaker as a formula**.  It is an existence statement about a
  different object, and its converse is not proved.
* It is **not an equivalent restatement** of the forbidden kinds (gap-sum bound, descent count,
  Parity, Arc, CurveSublistStep, Pinched).  It mentions neither `gapSum` nor descents.  It does
  not ask that the steps of `l` be forward in `w`.

## Intended witness, and truth (LOUD)

* `N` is the **mirror** `(α, σ⁻¹)` of `reclosedMap X.toCombMap (sideFaces X.toCombMap K.walk)`.
  Its Euler characteristic is that of `X` by the premise `hinner`, and `X.planar` holds.
* `ι` is the kept-dart inclusion and `l'` is `l` pulled back.
* `Γ` is the reclosed pocket face, read in `w`'s orientation.
* The successor rule `turn_next` of `EnclosedFaceSetSucc` reads backwards on `l = invDarts`.  That
  is why the mirror appears.
* Deleting internal edges only removes unkept darts from a rotation, so first-kept steps survive.
* `w` is read along the reclosed boundary cycle, so the order compatibility holds.
* `SP/gl-p07-60/bridge_check.py` tests this witness on the gl-p07-59 models, with `N` the mirror,
  `ι = id` and `Γ = w`.  It checks the successor steps, that `w` is a face cycle of `N`, that
  `l ⊆ w`, and compatibility.  There are **0 failures in 26488 flower configurations and 14096
  genus-0 random configurations**.
* NOT model-checked: reclosing a multi-face pocket.  In the models the curve is already one face.
  The risk is a pinch vertex of the pocket boundary, where reclosing may split the vertex and
  change a rotation.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- `c` comes strictly before `d` in the list `L`. -/
def WitnessStepGenusBefore {γ : Type*} (L : List γ) (c d : γ) : Prop :=
  ∃ u v z : List γ, L = u ++ c :: (v ++ d :: z)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepGenusBefore

/-- **Residual of lane gl-p07-60: a planar model of the curve.**  The premises of
`WitnessStepWindingPinchedStatement`.  The conclusion: a planar map `N` and a list `l'` over it
that maps onto `invDarts X outerWalk`, whose cyclic steps are successor steps of `N`, which lies on
one face cycle `Γ` of `N`, and on which `witnessSublistCurve a b G₁ G₂` has the order of `Γ`.
LOUD: smaller in proof content (the genus-zero argument is discharged); not claimed strictly
weaker as a formula. -/
def WitnessStepGenusBridgeStatement : Prop :=
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
        (∃ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
          (invDarts X outerWalk).rotate n = s ++ x :: y :: t ∧
          ¬ WitnessStepCellTurn G₁ G₂ outerWalk y ∧
          ¬ WitnessStepSideTurn a b G₁ G₂ outerWalk y ∧
          ¬ WitnessStepBlockTurn a b G₁ G₂ x y ∧
          ¬ WitnessStepCornerTurn a b G₁ G₂ outerWalk y ∧
          WitnessStepPinchOffAt a b K C.face G₁ G₂ outerWalk x y) →
        ∃ (N : CombMap.{v}) (ι : N.Dart → X.toCombMap.Dart) (l' Γ : List N.Dart),
          N.IsPlanar ∧ l'.map ι = invDarts X outerWalk ∧
          (∀ (n : ℕ) (s t : List N.Dart) (c d : N.Dart), l'.rotate n = s ++ c :: d :: t →
            WitnessStepGenusSucc N l' c d) ∧
          N.IsFaceCycle Γ ∧ (∀ d ∈ l', d ∈ Γ) ∧
          ∀ c ∈ l', ∀ d ∈ l',
            (WitnessStepGenusBefore (witnessSublistCurve a b G₁ G₂) (ι c) (ι d) ↔
              WitnessStepGenusBefore Γ c d)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepGenusBridgeStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
