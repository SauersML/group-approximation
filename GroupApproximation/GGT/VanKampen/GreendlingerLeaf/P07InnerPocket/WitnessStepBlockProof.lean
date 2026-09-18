import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBlockStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBlockStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-49: the side residual from the residual off block turns

Lane gl-p07-49.  This file proves `FourPieceWitness.WitnessStepSideResidualStatement`
(`WitnessStepSideStatement.lean`) from `FourPieceWitness.WitnessStepBlockResidualStatement`
(`WitnessStepBlockStatement.lean`).  Certifies no printed sentence on its own.

Route: the backward disjunct passes through unchanged.  In the forward disjunct, take a
consecutive pair `(x, y)` of a rotation of `l` with no cell turn and no side turn at `y`.  If
`(x, y)` is not a block-order turn, the new residual gives the step.  If it is, `y ∈ l` (it sits in
the rotation), so `y ∈ w` by the step 1 label (`witnessSublist_mem_curve`), and
`witnessStepBlock_step_of_blockTurn` gives the forward step.

LOUD: the new residual is logically equivalent to the old one, given this reduction.  It is
strictly smaller only in proof content, and the discharged part is list-level only.  See
`WitnessStepBlockStatement.lean`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Lane gl-p07-49: the side residual from the residual off block-order turns.** -/
theorem witnessStepSideResidual_of_witnessStepBlock
    (h : WitnessStepBlockResidualStatement.{u, w, v}) :
    WitnessStepSideResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      hlab with hfwd | hbwd
  · refine Or.inl fun n s t x y hr hcell hside => ?_
    by_cases hblock : WitnessStepBlockTurn a b G₁ G₂ x y
    · have hyl : y ∈ invDarts X outerWalk := (List.mem_rotate (n := n)).mp (by rw [hr]; simp)
      have hyw : y ∈ witnessSublistCurve a b G₁ G₂ := witnessSublist_mem_curve (hlab y hyl)
      exact witnessStepBlock_step_of_blockTurn hyw hblock
    · exact hfwd n s t x y hr hcell hside hblock
  · exact Or.inr hbwd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSideResidual_of_witnessStepBlock

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
