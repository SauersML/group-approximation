import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCells
import GroupApproximation.Meta.AxiomGuard

/-!
# The pick-run statement when every walk class holds a relator cell

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-37.

## LOUD: `ExtremalJordanPickRunStatement` may be FALSE (G-faces)

This file does NOT prove `ExtremalJordanPickRunStatement`.  In the G-face model, all relator
cells of `K.faces` sit in one adversarial inside region and every other inside region is made of
G-faces only (script `gl-p10-37/gw.py`).  There, clause (a) (some pool class) FAILS at 7 darts,
with 16 failures at vertex degree at most 3.  Example: vertices `[2,0,0,2,1,1,2]`, (inside,
outside) regions `[(0,1),(2,1),(3,1),(2,1),(4,1),(5,1),(4,1)]`, reversed source arc `[1,2,3]`,
target arc `[4,5,6]`, source region = exterior region = `1`, cell region `0`.  These are three
petals at one vertex.  The side loop bounds the petal of all relator cells.  The source and
target digons each hold a G-face balloon loop.  Each arc then reads classes `Z W Z`, so no class
meets an arc through one end.  The labels `comp λ 1` (balloons) and `g, g⁻¹` (digons) are legal
letters.  LeastArea, the arc-length premises and the chord premise were not certified in the
model.

So the following are POSSIBLY FALSE:

* `ExtremalJordanPickRunStatement`, and through clause (a) also `ExtremalJordanPickStatement`,
  `ExtremalJordanRerouteStatement` and `ExtremalJordanStatement`.
* `ExtremalJordanPickStepUniformStatement` (lane gl-p10-36).  Take 5 darts at one vertex with
  regions `[(0,1),(2,1),(3,1),(4,1),(5,1)]`, reversed source arc `[1,2]`, target arc `[3,4]`,
  source = exterior = `1` and cell region `0`.  Pool classes exist, but none is uniform.
* The descent (b1): 3,168 instances at 7 darts of degree at most 3 have pool classes, but none
  with at most two changes.

Any residual `R` with `Three ∧ R → (a)` is FALSE in this model, because Three holds there.

## The isolated Statement

`ExtremalJordanPickCellsRunStatement` is `ExtremalJordanPickRunStatement` with one more
hypothesis, `ExtremalJordanPickCellsClass K`: every walk class holds a relator cell of `K.faces`.
It is logically WEAKER than `ExtremalJordanPickRunStatement`
(`extremalJordanPickCells_cellsRun_of_run`).  It is not an equivalent restatement, because the
counterexample above violates the extra hypothesis.  It is reduced to:

* `ExtremalJordanPickRegionThreeStatement` (lane gl-p10-35/38), for clause (a); and
* `ExtremalJordanPickStepUniformStatement` (lane gl-p10-36)
  (`extremalJordanPickCells_run_of_three`), or its weaker cells form
  `ExtremalJordanPickCellsStepStatement` (`extremalJordanPickCells_run_of_three_cellsStep`), or a
  descent under the premises (`extremalJordanPickCells_run_of_three_desc`), for clause (b1).

`ExtremalJordanPickCellsRegionStatement` (clause (a) for regions) follows from Three alone.  It
is logically STRONGER than the lane-35 `ExtremalJordanPickRegionCellsStatement`, because it has a
weaker hypothesis (`extremalJordanPickCells_regionCells_of_cellsRegion`).

## Truth check (model, script `gl-p10-37/gwc.py`)

The model takes the least relator-cell set allowed by the hypothesis: the inside regions of the
walk darts.  G-faces fill every other inside region.

| darts | vertex degree | instances | region class | pool class | uniform class, ≤ 2 changes |
|-------|---------------|-----------|--------------|------------|----------------------------|
| ≤ 5   | any           | 228,756   | all          | all        | all                        |
| ≤ 6   | any           | 6,717,858 | all          | all        | all                        |
| 7     | at most 3     | 751,422   | all          | all        | all                        |

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **Clause (a) for regions, cells form.**  This is `ExtremalJordanPickRegionCellsStatement`
with the lane-35 hypothesis (relator cells on the walk) weakened to
`ExtremalJordanPickCellsClass K`.  It follows from the Three statement
(`extremalJordanPickCells_region_of_three`). -/
def ExtremalJordanPickCellsRegionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
      ExtremalJordanPickCellsClass K →
        ∃ r : X.toCombMap.Dart, ExtremalJordanPickPoolRegion K r

/-- **The isolated Statement.**  This is `ExtremalJordanPickRunStatement` with one more
hypothesis, `ExtremalJordanPickCellsClass K`.  LOUD: logically WEAKER than
`ExtremalJordanPickRunStatement`, which may be FALSE (module docstring).  It held in the model
with every walk class holding a relator cell. -/
def ExtremalJordanPickCellsRunStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
      ExtremalJordanPickCellsClass K →
        (∃ r : X.toCombMap.Dart, ExtremalJordanPickPool K r) ∧ ExtremalJordanPickRunDescent K

/-- **The uniform step, cells form.**  This is `ExtremalJordanPickStepUniformStatement` with one
more hypothesis, `ExtremalJordanPickCellsClass K`.  It is logically WEAKER than that statement
(`extremalJordanPickCells_cellsStep_of_step`), which may be FALSE (module docstring). -/
def ExtremalJordanPickCellsStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
      ExtremalJordanPickCellsClass K →
      (∃ r : X.toCombMap.Dart, ExtremalJordanPickPool K r) →
        ∃ r : X.toCombMap.Dart, ExtremalJordanPickStepUniform K r ∧
          ExtremalJordanPickChanges K r ≤ 2

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickCellsRegionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickCellsRunStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickCellsStepStatement
