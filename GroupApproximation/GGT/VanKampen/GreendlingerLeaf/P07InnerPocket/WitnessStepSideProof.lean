import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSideStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSideStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-47: the step residual from the residual off side turns

Lane gl-p07-47.  This file proves `FourPieceWitness.WitnessStepResidualStatement`
(`WitnessCurveStepStatement.lean`) from `FourPieceWitness.WitnessStepSideResidualStatement`
(`WitnessStepSideStatement.lean`).  Certifies no printed sentence on its own.

Route: the backward disjunct passes through unchanged.  In the forward disjunct, take a
consecutive pair `(x, y)` with no cell turn at `y`.  If there is no side turn at `y` either, the
new residual gives the step.  For a side turn along `b.sideFrom i`, use
`witnessStepSide_step_of_turnB` with `not_mem_right_of_mem_witnessFaces` (this uses `C.face ∉ b.1`).
For one along `a.sideFrom j`, use `witnessStepSide_step_of_turnA` with
`not_mem_left_of_mem_witnessFaces` (this uses `C.face ∉ a.1`).

LOUD: the new residual is logically equivalent to the old one, given this reduction.  It is
strictly smaller only in proof content.  See `WitnessStepSideStatement.lean`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Lane gl-p07-47: the step residual from the residual off the cell and side turns.** -/
theorem witnessStepResidual_of_witnessStepSide
    (h : WitnessStepSideResidualStatement.{u, w, v}) :
    WitnessStepResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      hlab with hfwd | hbwd
  · refine Or.inl fun n s t x y hr hcell => ?_
    by_cases hside : WitnessStepSideTurn a b G₁ G₂ outerWalk y
    · unfold WitnessStepSideTurn at hside
      rcases hside with ⟨p, q, g, hg, hS, hyB⟩ | ⟨p, q, g, hg, hS, hyA, hg2, hgb⟩
      · exact witnessStepSide_step_of_turnB E hnb hlab
          (fun f hf => not_mem_right_of_mem_witnessFaces hCb hf) hr hS hg hyB
      · exact witnessStepSide_step_of_turnA E hnb
          (fun f hf => not_mem_left_of_mem_witnessFaces hCa hf) hr hS hg hyA hg2 hgb
    · exact hfwd n s t x y hr hcell hside
  · exact Or.inr hbwd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepResidual_of_witnessStepSide

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
