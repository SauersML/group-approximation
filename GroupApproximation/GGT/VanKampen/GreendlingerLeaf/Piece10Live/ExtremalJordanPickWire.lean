import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCountBoundWire
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCellsWire
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickUniform
import GroupApproximation.Meta.AxiomGuard

/-!
# Wiring the closed count statements into the pick chain

Lane gl-p10-45, pure wiring.  `Piece10Live/ExtremalJordanPickCountBoundWire` closes the Euler
class count, the three-class count and the Three statement with no hypotheses.  This file feeds
them into every consumer in the pick chain whose hypothesis they discharge:

* the region statement for the cells case (`ExtremalJordanPickRegionCellsStatement`) and its
  cells-class form (`ExtremalJordanPickCellsRegionStatement`) now hold outright;
* the TwoOutside statement (`ExtremalJordanPickThreeTwoOutsideStatement`) now holds outright;
* the cells run form (`ExtremalJordanPickCellsRunStatement`) now needs only clause (b1): the
  cells step form, the uniform step, its loop-free case, or a descent.

No new mathematics: every proof is an application of an existing `_of_` reduction.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **The region statement for the cells case** holds outright. -/
theorem extremalJordanPickWire_regionCells : ExtremalJordanPickRegionCellsStatement.{u, w, v} :=
  extremalJordanPickRegion_region_of_three extremalJordanPickCountBound_three

/-- **The cells-class region statement** holds outright. -/
theorem extremalJordanPickWire_cellsRegion : ExtremalJordanPickCellsRegionStatement.{u, w, v} :=
  extremalJordanPickCells_region_of_three extremalJordanPickCountBound_three

/-- **The TwoOutside statement** holds outright. -/
theorem extremalJordanPickWire_twoOutside :
    ExtremalJordanPickThreeTwoOutsideStatement.{u, w, v} :=
  extremalJordanPickCount_twoOutside_of_euler extremalJordanPickCountBound_euler

/-- **The cells run form from the cells step form** alone. -/
theorem extremalJordanPickWire_cellsRun_of_cellsStep
    (hstep : ExtremalJordanPickCellsStepStatement.{u, w, v}) :
    ExtremalJordanPickCellsRunStatement.{u, w, v} :=
  extremalJordanPickCells_run_of_three_cellsStep extremalJordanPickCountBound_three hstep

/-- **The cells run form from the uniform step** alone. -/
theorem extremalJordanPickWire_cellsRun_of_step
    (hstep : ExtremalJordanPickStepUniformStatement.{u, w, v}) :
    ExtremalJordanPickCellsRunStatement.{u, w, v} :=
  extremalJordanPickCells_run_of_three extremalJordanPickCountBound_three hstep

/-- **The cells run form from the loop-free uniform step** alone. -/
theorem extremalJordanPickWire_cellsRun_of_uniform
    (h : ExtremalJordanPickUniformStatement.{u, w, v}) :
    ExtremalJordanPickCellsRunStatement.{u, w, v} :=
  extremalJordanPickCells_run_of_three extremalJordanPickCountBound_three
    (extremalJordanPickUniform_step_of_loopFree h)

/-- **The cells run form from a descent** for every pocket that meets the premises and the cells
hypothesis. -/
theorem extremalJordanPickWire_cellsRun_of_desc
    (hdesc : ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
      (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
      hi ≤ (outerDarts X).length → X.LeastArea →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
        K.sourceArc.length < (cellDarts X K.source).length →
        K.targetArc.length < (outerDarts X).length →
        ¬Unpinched X.toCombMap K.faces →
        P10ChordLift.AllNonFirstTurnsCrossed K →
        ExtremalJordanPickCellsClass K → ExtremalJordanPickRunDescent K) :
    ExtremalJordanPickCellsRunStatement.{u, w, v} :=
  extremalJordanPickCells_run_of_three_desc extremalJordanPickCountBound_three hdesc

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickWire_regionCells
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickWire_cellsRegion
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickWire_twoOutside
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickWire_cellsRun_of_cellsStep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickWire_cellsRun_of_step
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickWire_cellsRun_of_uniform
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickWire_cellsRun_of_desc
