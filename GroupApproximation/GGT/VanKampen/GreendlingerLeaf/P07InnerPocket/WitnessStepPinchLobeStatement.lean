import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchCutStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-55: only the open entries before `y` at an off-lobe pinch

Lane gl-p07-55.  The target is `FourPieceWitness.WitnessStepPinchCutStatement`
(`WitnessStepPinchCutStatement.lean`, lane gl-p07-54).  This file states the residual
`FourPieceWitness.WitnessStepPinchLobeStatement`.  `WitnessStepPinchLobeProof.lean` proves the
target from it (`witnessStepPinchLobe_pinchCut_of_pinchLobe`), and also proves the converses, so the
chain `PinchOff ↔ PinchCut ↔ PinchLobe` is recorded in Lean.  Certifies no printed sentence on its
own.  NOT COMPILED: this lane was authored without running Lean.

## Notation

`w = witnessSublistCurve a b G₁ G₂`, `l = invDarts X ow`, `F = witnessFaces a b K c`.  An entry
`e` of `w` is **open** when `IsOpenFace a b K c (faceOf e)`: its face is on the side of `K.walk`
and off the cut.

## The residual

Same premise block and same backward disjunct as the target.  At an off-lobe pinch `(x, y)` with
`w = pre ++ y :: (mid ++ x :: post)`, it asks only: **every open entry of `pre` is off `l`**.

## Route of the reduction (`WitnessStepPinchLobeFace.lean`, `WitnessStepPinchLobeProof.lean`)

Let `e ∈ pre` with `faceOf e ∈ F`.
* `F` consists of open faces (`mem_witnessFaces_iff`), so `e` is open.  This discharges every
  closed entry of `pre`, among them the lobe dart `α g` (its face is not open, by the off-lobe
  pinch data).
* `e` is an entry of the curve, so `α e` lies on a piece `G₁`, `b.sideFrom i`, `G₂`, `a.sideFrom j`
  (`witnessStepPinchLobe_alpha_mem_pieces`).  Its face is off `F`
  (`witnessStepPinchOff_faceOf_not_mem`).  As `faceOf (α (α e)) = faceOf e ∈ F`, `mem_iff` of the
  enclosing walk gives `α e ∈ ow`, so `e ∈ l` (`witnessStepPinchLobe_mem_of_faceOf_mem`).
* The residual says `e ∉ l`.  Contradiction.

## The converses (also in `WitnessStepPinchLobeProof.lean`)

* `WitnessStepPinchCutStatement → WitnessStepPinchLobeStatement`: an entry `e ∈ l` has
  `faceOf e ∈ F` by `hnb`.
* `WitnessStepPinchOffStatement → WitnessStepPinchCutStatement` (the converse gl-p07-54 argued
  on paper).  Its forward `StepNext w l x y`, with `y` before `x`, cannot be the first clause, as
  `w` has no duplicates (`witnessStepPinchLobe_not_both`).  So it is the wrap-around clause, whose
  prefix is `pre` (`append_cons_inj_of_nodup`) and is off `l`.  An entry of `pre` with face in `F`
  would be in `l`, by the translation above.

## Truth check (Python model, `SP/gl-p07-55/pinch_lobe_model.py`, scratchpad, not built)

The planar flowers of `SP/gl-p07-54/pinch_cut_model.py` (`k ≤ 4` petals of types triangle, double
petal, sub-petal at a second pinch vertex; every cut mask, start face and linearisation).

| k | pinches | `y` before `x` | residual holds | some open entry in `pre` | loop-A form holds |
|---|---------|----------------|----------------|--------------------------|-------------------|
| 1 | 12      | 8              | 8              | 0                        | 8                 |
| 2 | 1112    | 636            | 636            | 172                      | 636               |
| 3 | 30947   | 15486          | 15486          | 5698                     | 15486             |
| 4 | 631355  | 274174         | 274174         | 116738                   | 274174            |

* The residual holds at every pinch with `y` before `x`.
* In about 57% of these (157436 of 274174 at `k = 4`) every entry of `pre` is closed.  There the
  residual is vacuous, and the reduction settles the target outright.
* The converse translation (`t ∈ w`, `t ∉ l` implies `faceOf t ∉ F`) holds at every curve entry.
* **Loop-A form** (stronger, not used): every entry of `pre ++ post` has face off `F`.  This is the
  statement that all of loop A is off `F`.  It holds at every such pinch.

## LOUD: equal in logical strength, strictly smaller in proof content

The residual is **logically equivalent** to `WitnessStepPinchCutStatement`, and both converses
are proved here (not only argued).  It is not strictly weaker and not stronger.  It is strictly
smaller in proof content: the reduction discharges
* every **closed** entry of `pre`, including the lobe dart `α g` that the gl-p07-54 model found
  as the last entry of every nonempty `pre`;
* the translation from "face in `F`" to "in `l`" for curve entries.

## What is left: the Jordan lobe-separation fact, open entries only

At an off-lobe pinch with `y` before `x`, an **open** curve entry before `y` is not on the
witness walk.  Paper route: `Γ` splits at the pinch vertex into loop A (from `g`) and loop B
(from `α x` to `α y`); the entries of `pre` are `α` of loop-A darts; `F` is Touch-connected and
lies in the lobe of loop B; an open face across loop A that met `F` would give a Touch path of open
faces from the lobe of B into the lobe of A, and such a path must pass a common vertex of the two
loops, where (at the pinch vertex) the lobe face is closed.  This needs a planar separation fact
for the split loops, which the repo does not have.  Grep of `P07InnerPocket` for
`Connected|Touch|interleave`: `WitnessPlanarCloseConnected` (face-set connectivity of the
**complement** and of the boundary map, under hypotheses), `RegionTouch*` (region cycles meet the
pocket walk) and `*Noninterleave*` (four-block residuals, themselves unproved).  None states that
Touch paths of open faces cannot cross a pinch.

## Notes

* **Backward disjunct kept**, as in the target.
* **No context-free form.**  The premise block is kept whole.  A Jordan statement stripped of the
  pocket premises is FALSE (the three-petal model in `P06LakeFree/EnclosedOrder.lean`).
* **AVOID list respected.**  No reduction to `RigidPolarSupportSeparation`,
  `RigidPolarCharacterization`, `KerNormallyGenerated`, `PocketFourPiece{LakeRead,WitnessPlanar,
  WitnessArcs}Statement`, `FrameConeFourStatement` or `ExtremalEndBlockStatement`; no surgery, no
  loose-count or minimal-count descent; the backward disjunct is not used as the covering case.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Residual of lane gl-p07-55: at an off-lobe pinch with `y` before `x` on the curve, every
open curve entry before `y` lies off the inverted enclosing walk.**  Same premises and the same
backward disjunct as `WitnessStepPinchCutStatement`.  LOUD: logically equivalent to that statement
(both directions are proved in `WitnessStepPinchLobeProof.lean`), and strictly smaller only in
proof content. -/
def WitnessStepPinchLobeStatement : Prop :=
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
              ∀ e ∈ pre, IsOpenFace a b K C.face (X.toCombMap.faceOf e) →
                e ∉ invDarts X outerWalk) ∨
          ∀ (n : ℕ) (s t : List X.toCombMap.Dart) (x y : X.toCombMap.Dart),
            (invDarts X outerWalk).rotate n = s ++ x :: y :: t →
            WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂)
              (invDarts X outerWalk) y x

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.WitnessStepPinchLobeStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
