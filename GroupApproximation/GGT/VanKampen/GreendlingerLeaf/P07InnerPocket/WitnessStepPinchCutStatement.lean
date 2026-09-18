import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchOffStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-54: the prefix before `y` at an off-lobe pinch

Lane gl-p07-54.  The target is `FourPieceWitness.WitnessStepPinchOffStatement`
(`WitnessStepPinchOffStatement.lean`, lane gl-p07-53).  This file states the residual
`FourPieceWitness.WitnessStepPinchCutStatement`.  `WitnessStepPinchCutProof.lean` proves the
target from it (`FourPieceWitness.witnessStepPinchCut_pinchOff_of_pinchCut`).  Certifies no printed
sentence on its own.  NOT COMPILED: this lane was authored without running Lean.

## Notation

`w = witnessSublistCurve a b G₁ G₂` (the inverted curve), `l = invDarts X ow` (the inverted
enclosing walk of `F = witnessFaces a b K c`).  A pair `(x, y)` is consecutive in a rotation of `l`.

## The residual

Same premise block as the target, and the same backward disjunct.  The forward disjunct no longer
asks for `StepNext w l x y`.  At an off-lobe pinch `(x, y)` with **`y` before `x` in `w`**, it asks
only that no entry of `w` before `y` lies on a witness face:
`w = pre ++ y :: (mid ++ x :: post) → ∀ e ∈ pre, faceOf e ∉ F`.

## Route of the reduction (`WitnessStepPinchCutProof.lean`)

* `l` has no duplicates (`E.nodup`), so `x ≠ y`.
* `x` and `y` lie in `w`: `hlab` places each entry of `l` on a piece of `w`
  (`witnessSublist_mem_curve`).
* So `x` is before `y` in `w`, or `y` is before `x` (`witnessStepPinchCut_order`).
  * If `x` is first, the first clause of `StepNext` holds.
  * If `y` is first, the residual gives `faceOf e ∉ F` on the prefix `pre`.  An entry `e ∈ pre`
    that lay in `l` would have `α e ∈ ow`, so `faceOf e = faceOf (α (α e)) ∈ F` by `hnb`.  So no
    entry of `pre` lies in `l`, which is the wrap-around clause of `StepNext`.

## Truth check (Python model, `SP/gl-p07-54/pinch_cut_model.py`, scratchpad, not built)

Planar flowers from coordinates, with `k = 1, ..., 4` petals of three types: a triangle, a double
petal, and a sub-petal at a second pinch vertex (so the witness set can spill by a vertex touch).
The model runs every open/cut mask, every start face, and every linearisation of the curve.  It
keeps only the configurations where `ow` is one cycle and `hlab` holds.

| k | pairs     | pinch fwd | pinch wrap | wrap via `α g` | configs with pinch | bwd holds |
|---|-----------|-----------|------------|----------------|--------------------|-----------|
| 1 | 149       | 4         | 8          | 6              | 12                 | 0         |
| 2 | 7203      | 476       | 636        | 524            | 982                | 0         |
| 3 | 186528    | 15461     | 15486      | 13337          | 24406              | 0         |
| 4 | 3650196   | 357181    | 274174     | 240917         | 423610             | 0         |

The model found:
* forward `StepNext` holds at every pair;
* the residual (prefix before `y` off `F`) holds at every pinch with `y` before `x`;
* the lobe face `faceOf (α g)` is always a cut face or the outer face;
* whenever the prefix is nonempty, its last entry is `α g`, the lobe dart.

**The backward disjunct never holds in a configuration with a pinch.**  So at cut-lobe pinches the
**forward** disjunct is the one that holds.  It holds via the wrap-around clause (about half the
pinches), where the entry of `w` just before `y` is `α g`.  The guess that the backward disjunct
covers them is REFUTED.

The residual is TRUE, provided the target is true: see the converse below.

## What is left: the Jordan lobe-separation fact

At an off-lobe pinch, `Γ` splits at the pinch vertex into loop A (from `g`) and loop B (from `α x`
to `α y`).  The witness faces lie in the lobe of loop B.  If `y` comes before `x` in `w`, every
entry of `w` before `y` is `α` of a loop-A dart, so its face is on the far side, off `F`.  This is
a planar separation fact about the pocket.  It needs the connectivity of the witness set (touches
do not interleave).  It is not proved here.

## LOUD: equal in logical strength, strictly smaller in proof content

The residual is **logically equivalent** to `WitnessStepPinchOffStatement`.  This is forced: any
residual that the target implies and that suffices for the target is equivalent to it.  The
converse direction is argued here and not formalised:
* the target's forward `StepNext` with `y` before `x` must be the wrap-around clause, by nodup of
  `w` (`witnessSublist_curve_nodup`);
* an entry `t` of `w` is `α` of a curve dart, and curve faces are off `F`
  (`witnessStepPinchOff_faceOf_not_mem`);
* so by `mem_iff`, `t ∉ l` gives `faceOf t ∉ F`.

It is **not** strictly weaker in logic, and it is not stronger.  It is strictly smaller in proof
content.  The reduction discharges:
* the forward case, and the order split of `x` and `y` in `w`;
* `x ≠ y`, from the nodup of the walk;
* `l ⊆ w`, from `hlab`;
* the translation from "not in `l`" to "face off `F`", via `hnb`.

Further notes:
* **Backward disjunct kept**, as in the target.  A version without it would be formally stronger.
  The model says it would still be true, but it is not needed.
* **No context-free form.**  The premise block is kept whole.  A Jordan statement stripped of the
  pocket premises is FALSE (the three-petal model in `P06LakeFree/EnclosedOrder.lean`).
* **AVOID list respected.**  No reduction to `RigidPolarSupportSeparation`,
  `RigidPolarCharacterization`, `KerNormallyGenerated`, `PocketFourPieceLakeReadStatement`,
  `PocketFourPieceWitnessPlanarStatement`, `PocketFourPieceWitnessArcsStatement`,
  `FrameConeFourStatement` or `ExtremalEndBlockStatement`.  No two-passage successor-exchange
  surgery, and no loose-count descent.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Residual of lane gl-p07-54: at an off-lobe pinch with `y` before `x` on the curve, the
curve prefix before `y` lies off the witness faces.**  Same premises and the same backward disjunct
as `WitnessStepPinchOffStatement`.  LOUD: logically equivalent to that statement (the converse is
argued in the module docstring), and strictly smaller only in proof content. -/
def WitnessStepPinchCutStatement : Prop :=
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
            ∀ pre mid post : List X.toCombMap.Dart,
              witnessSublistCurve a b G₁ G₂ = pre ++ y :: (mid ++ x :: post) →
              ∀ e ∈ pre, X.toCombMap.faceOf e ∉ witnessFaces a b K C.face) ∨
          ∀ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
            (invDarts X outerWalk).rotate n = s ++ x :: y :: t →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) y x

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepPinchCutStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
