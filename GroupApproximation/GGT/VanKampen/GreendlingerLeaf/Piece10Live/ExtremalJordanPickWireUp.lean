import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickWire
import GroupApproximation.Meta.AxiomGuard

/-!
# Wiring the pick chain up to the relative Greendlinger statement

Lane gl-p10-45, pure wiring.  With the Three statement closed
(`extremalJordanPickCountBound_three`), the pick chain reaches
`RelativeGreendlingerQuasiGeodesicLeastAreaStatement` from three inputs:

* `hoff : P07InnerPocket.PocketFourPieceOffStatement` (the P07 lane);
* clause (b1): `ExtremalJordanPickStepUniformStatement`, or its loop-free case
  `ExtremalJordanPickUniformStatement`, or the cells step form;
* the cells hypothesis for every pocket (`hcls`).

LOUD: `hcls` FAILS in the G-face model, where inner faces of value 1 are not relator cells, and
there `ExtremalJordanPickRunStatement` and `ExtremalJordanPickStepPoolStatement` may be FALSE (the
model does not certify `LeastArea`).  So these wires are conditional endpoints, not a route that
is known to close.  The live frontier stays at `AssemblyResidual.relativeGreendlinger_of_residuals`.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **Clause (a) from the cells hypothesis for every pocket.**  LOUD: `hcls` fails in the G-face
model. -/
theorem extremalJordanPickWire_stepPool_of_cells
    (hcls : ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
      (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
      hi ≤ (outerDarts X).length → X.LeastArea →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
        K.sourceArc.length < (cellDarts X K.source).length →
        K.targetArc.length < (outerDarts X).length →
        ¬Unpinched X.toCombMap K.faces →
        P10ChordLift.AllNonFirstTurnsCrossed K → ExtremalJordanPickCellsClass K) :
    ExtremalJordanPickStepPoolStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact extremalJordanPickCells_pool_exists K
    (extremalJordanPickCountBound_three D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt
      hpinch hrose)
    (hcls D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose)

/-- **The run statement from the uniform step and the cells hypothesis.**  LOUD: `hcls` fails in
the G-face model. -/
theorem extremalJordanPickWire_run_of_step_cells
    (hstep : ExtremalJordanPickStepUniformStatement.{u, w, v})
    (hcls : ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
      (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
      hi ≤ (outerDarts X).length → X.LeastArea →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
        K.sourceArc.length < (cellDarts X K.source).length →
        K.targetArc.length < (outerDarts X).length →
        ¬Unpinched X.toCombMap K.faces →
        P10ChordLift.AllNonFirstTurnsCrossed K → ExtremalJordanPickCellsClass K) :
    ExtremalJordanPickRunStatement.{u, w, v} :=
  extremalJordanPickStep_extremalJordanPickRun (extremalJordanPickWire_stepPool_of_cells hcls)
    hstep

/-- **The Jordan arc-end statement from the uniform step and the cells hypothesis.**  LOUD:
`hcls` fails in the G-face model. -/
theorem extremalJordanPickWire_extremalJordan_of_step_cells
    (hstep : ExtremalJordanPickStepUniformStatement.{u, w, v})
    (hcls : ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
      (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
      hi ≤ (outerDarts X).length → X.LeastArea →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
        K.sourceArc.length < (cellDarts X K.source).length →
        K.targetArc.length < (outerDarts X).length →
        ¬Unpinched X.toCombMap K.faces →
        P10ChordLift.AllNonFirstTurnsCrossed K → ExtremalJordanPickCellsClass K) :
    ExtremalJordanStatement.{u, w, v} :=
  extremalJordanPickRun_extremalJordan (extremalJordanPickWire_run_of_step_cells hstep hcls)

/-- **The relative Greendlinger statement from the four-piece-off statement, the uniform step
and the cells hypothesis.**  LOUD: `hcls` fails in the G-face model. -/
theorem extremalJordanPickWire_relativeGreendlinger_of_step_cells
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (hstep : ExtremalJordanPickStepUniformStatement.{u, w, v})
    (hcls : ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
      (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
      hi ≤ (outerDarts X).length → X.LeastArea →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
        K.sourceArc.length < (cellDarts X K.source).length →
        K.targetArc.length < (outerDarts X).length →
        ¬Unpinched X.toCombMap K.faces →
        P10ChordLift.AllNonFirstTurnsCrossed K → ExtremalJordanPickCellsClass K) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  extremalJordanPickRun_relativeGreendlinger hoff
    (extremalJordanPickWire_run_of_step_cells hstep hcls)

/-- **The relative Greendlinger statement from the loop-free uniform step.**  LOUD: `hcls` fails
in the G-face model. -/
theorem extremalJordanPickWire_relativeGreendlinger_of_uniform_cells
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : ExtremalJordanPickUniformStatement.{u, w, v})
    (hcls : ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
      (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
      hi ≤ (outerDarts X).length → X.LeastArea →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
        K.sourceArc.length < (cellDarts X K.source).length →
        K.targetArc.length < (outerDarts X).length →
        ¬Unpinched X.toCombMap K.faces →
        P10ChordLift.AllNonFirstTurnsCrossed K → ExtremalJordanPickCellsClass K) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  extremalJordanPickWire_relativeGreendlinger_of_step_cells hoff
    (extremalJordanPickUniform_step_of_loopFree h) hcls

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickWire_stepPool_of_cells
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickWire_run_of_step_cells
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickWire_extremalJordan_of_step_cells
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickWire_relativeGreendlinger_of_step_cells
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickWire_relativeGreendlinger_of_uniform_cells
