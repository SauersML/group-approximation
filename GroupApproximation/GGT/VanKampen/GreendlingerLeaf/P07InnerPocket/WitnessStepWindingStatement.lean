import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepDescentStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-59: winding one on pinched configurations only

Lane gl-p07-59.  States the residual `FourPieceWitness.WitnessStepWindingPinchedStatement`.
Certifies no printed sentence on its own.  NOT COMPILED: authored without running Lean.

## The residual

Write `w = witnessSublistCurve a b G₁ G₂`, `l = invDarts X outerWalk`, `F = witnessFaces a b K c`.
The premise block and both disjuncts are those of `WitnessStepDescentStatement` (lane gl-p07-58).
There is one extra hypothesis: **the configuration is pinched**.  Some rotation step `(x, y)` of `l`
has no cell, side, block-order or corner turn, and is an off-lobe pinch
(`WitnessStepPinchOffAt a b K c G₁ G₂ outerWalk x y`).  Under it, the residual asks for the same
winding-one bound: the gap sum of the steps of `l`, indexed by first occurrence in `w`, is at most
`|w|`.

## Route of the reduction (`WitnessStepWindingProof.lean`)

* Every rotation step of `l` is a forward `StepNext` of `w`.  Then the bound is
  `witnessStepDescent_bound_of_steps` (gl-p07-58).  It is proved from the telescoping identity and
  the uniqueness of the first entry.
* Otherwise some step `(x, y)` is not a `StepNext`.  `witnessStepPinchArc_classify` (gl-p07-57)
  makes that step an off-lobe pinch with no cell, side, block or corner turn.  The configuration
  is therefore pinched, and the residual applies.

## Strength (LOUD)

* **Strictly weaker as a formula** than `WitnessStepDescentStatement`.  It has the same
  conclusion and one extra hypothesis, so `WitnessStepDescentStatement → this` is immediate.
* It is **not vacuous**.  In the model, 423610 of 435196 flower configurations are pinched (below).
  The extra hypothesis says only that a pinch occurs.  It does not say that a step fails
  `StepNext`, which never happens in the model.
* **Logically equivalent under the premise block, since both statements are true.**  The reduction
  closes the unpinched case, but the geometric input is still winding number one.  That input is
  now needed only where the curve pinches off a lobe at a vertex of the enclosing walk.  This lane
  does NOT close it.

## Why no local per-step invariant closes it (truth check, LOUD)

`SP/gl-p07-59/random_maps.py` uses random connected combinatorial maps: `σ` random, `α` a random
fixed-point-free involution, and `F` a random face set.  A case is kept when `ow` (successor rule)
is one cycle and all of `ow` lies on one face orbit `Γ` (the `hlab` model).  In 81895 such cases:
* 948 cases have `ow` with **two or more descents** against `Γ`; every one has genus > 0.
* In the 34881 genus-0 cases there are **no** failures.

The successor rule, the off-`F` fan of each step (`WitnessStepPinchFan`) and every other
per-vertex rotation fact hold in all these maps by construction.  So no invariant read off the
rotation system at single vertices can imply winding one.  The residual needs the genus-0 input,
`X.planar` or the Euler hypotheses on `reclosedMap`, globally.

`SP/gl-p07-59/winding_model.py` checks the planar flowers of gl-p07-58, with 1-4 petals of types
T/D/S, every cut mask, every start face and every linearisation of `Γ`.  The gap sum is at most
`|w|` in all 435196 configurations, and 423610 of them are pinched (a step `(x, y)` with the
`Γ`-next dart of `α y` off `ow`).  With random non-planar rotation systems on the same graphs
(1840 maps, 81803 kept cases) no failure appeared.  The flower `F` is too small to wind twice,
which is why the counterexamples come from `random_maps.py`.

## Suggested next route (not done here)

The genus-0 statement that `random_maps.py` supports: in a connected genus-0 map, if the successor
walk `ow` of a face set is one cycle and lies on one face orbit `Γ`, then `ow` is a cyclic
subsequence of `Γ`.  To use it here, apply it in `reclosedMap X.toCombMap (sideFaces ..)`, whose
Euler characteristic is `X`'s by hypothesis.  The open step is to show that `w` restricted to `l`
is read along a face orbit of that map.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Residual of lane gl-p07-59: winding one on pinched configurations.**  The premises and
the two disjuncts of `WitnessStepDescentStatement`, with the extra hypothesis that some rotation
step of `invDarts X outerWalk` has no cell, side, block or corner turn and is an off-lobe pinch.
LOUD: strictly weaker as a formula, and equivalent under the premises, since both are true. -/
def WitnessStepWindingPinchedStatement : Prop :=
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
        witnessStepDescent_gapSum
            (fun e => witnessStepDescent_pos e (witnessSublistCurve a b G₁ G₂))
            (witnessSublistCurve a b G₁ G₂).length
            (witnessStepDescent_steps (invDarts X outerWalk)) ≤
          (witnessSublistCurve a b G₁ G₂).length ∨
          ∀ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
            (invDarts X outerWalk).rotate n = s ++ x :: y :: t →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) y x

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepWindingPinchedStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
