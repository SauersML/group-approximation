import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCellsRun
import GroupApproximation.Meta.AxiomGuard

/-!
# Wiring the cells form of the pick-run statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-37.

These are the reductions for `ExtremalJordanPickCellsRunStatement`
(`Piece10Live/ExtremalJordanPickCellsRun`).  Clause (a) comes from the Three statement through
`extremalJordanPickCells_pool_exists`.  Clause (b1) comes from the uniform step, from its cells
form, or from a descent under the premises.  The comparison theorems show that each cells form is
logically weaker than the unrestricted statement, except for the region form, which is stronger
than the lane-35 region form.

LOUD: `extremalJordanPickCells_run_of_cellsRun` recovers `ExtremalJordanPickRunStatement` only
from the extra hypothesis for every pocket.  That hypothesis FAILS in the G-face model, and there
`ExtremalJordanPickRunStatement` itself may be FALSE (see `ExtremalJordanPickCellsRun`).

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **Clause (a) for regions from the Three statement**, cells form. -/
theorem extremalJordanPickCells_region_of_three
    (h : ExtremalJordanPickRegionThreeStatement.{u, w, v}) :
    ExtremalJordanPickCellsRegionStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hcls
  exact extremalJordanPickCells_region_exists K
    (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose) hcls

/-- **The cells region form is stronger than the lane-35 form**: it has the weaker hypothesis. -/
theorem extremalJordanPickCells_regionCells_of_cellsRegion
    (h : ExtremalJordanPickCellsRegionStatement.{u, w, v}) :
    ExtremalJordanPickRegionCellsStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hcell
  exact h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
    (extremalJordanPickCells_class_of_cells K hcell)

/-- **The cells run form is weaker than `ExtremalJordanPickRunStatement`.** -/
theorem extremalJordanPickCells_cellsRun_of_run
    (h : ExtremalJordanPickRunStatement.{u, w, v}) :
    ExtremalJordanPickCellsRunStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose _
  exact h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose

/-- **The cells step form is weaker than `ExtremalJordanPickStepUniformStatement`.** -/
theorem extremalJordanPickCells_cellsStep_of_step
    (h : ExtremalJordanPickStepUniformStatement.{u, w, v}) :
    ExtremalJordanPickCellsStepStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose _ hex
  exact h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hex

/-- **The cells run form from Three and the cells step form.** -/
theorem extremalJordanPickCells_run_of_three_cellsStep
    (h : ExtremalJordanPickRegionThreeStatement.{u, w, v})
    (hstep : ExtremalJordanPickCellsStepStatement.{u, w, v}) :
    ExtremalJordanPickCellsRunStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hcls
  have hex : ∃ r : X.toCombMap.Dart, ExtremalJordanPickPool K r :=
    extremalJordanPickCells_pool_exists K
      (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose) hcls
  obtain ⟨r, hr, hle⟩ :=
    hstep D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hcls hex
  exact ⟨hex, extremalJordanPickRun_descent_of_exists_le_two K
    ⟨r, extremalJordanPickStep_pool_of_uniform K hr, hle⟩⟩

/-- **The lane endpoint**: the cells run form from Three and the uniform step of lane
gl-p10-36. -/
theorem extremalJordanPickCells_run_of_three
    (h : ExtremalJordanPickRegionThreeStatement.{u, w, v})
    (hstep : ExtremalJordanPickStepUniformStatement.{u, w, v}) :
    ExtremalJordanPickCellsRunStatement.{u, w, v} :=
  extremalJordanPickCells_run_of_three_cellsStep h
    (extremalJordanPickCells_cellsStep_of_step hstep)

/-- **The lane endpoint, descent form**: the cells run form from Three and a descent for every
pocket that meets the premises and the cells hypothesis. -/
theorem extremalJordanPickCells_run_of_three_desc
    (h : ExtremalJordanPickRegionThreeStatement.{u, w, v})
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
    ExtremalJordanPickCellsRunStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hcls
  exact ⟨extremalJordanPickCells_pool_exists K
      (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose) hcls,
    hdesc D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hcls⟩

/-- **Back to `ExtremalJordanPickRunStatement`** from the cells run form and the cells hypothesis
for every pocket.  LOUD: that hypothesis fails in the G-face model. -/
theorem extremalJordanPickCells_run_of_cellsRun
    (h : ExtremalJordanPickCellsRunStatement.{u, w, v})
    (hcls : ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
      (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
      hi ≤ (outerDarts X).length → X.LeastArea →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
        K.sourceArc.length < (cellDarts X K.source).length →
        K.targetArc.length < (outerDarts X).length →
        ¬Unpinched X.toCombMap K.faces →
        P10ChordLift.AllNonFirstTurnsCrossed K → ExtremalJordanPickCellsClass K) :
    ExtremalJordanPickRunStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
    (hcls D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCells_region_of_three
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCells_regionCells_of_cellsRegion
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCells_cellsRun_of_run
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCells_cellsStep_of_step
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCells_run_of_three_cellsStep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCells_run_of_three
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCells_run_of_three_desc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCells_run_of_cellsRun
