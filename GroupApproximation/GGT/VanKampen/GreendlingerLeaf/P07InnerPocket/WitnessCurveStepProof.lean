import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveStepStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveStepCell
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-40: the witness step from the residual off the cell turns

Lane gl-p07-40.  This file proves `FourPieceWitness.WitnessCurveSublistStepStatement`
(`WitnessCurveSublistStatement.lean`) from `FourPieceWitness.WitnessStepResidualStatement`
(`WitnessCurveStepStatement.lean`).  Certifies no printed sentence on its own.

Route: the backward disjunct passes through unchanged.  In the forward disjunct, take a
consecutive pair `(x, y)` of a rotation of `l`.  If there is no cell turn at `y`, the residual
gives the step.  If there is a cell turn along `G₁`, use `witnessStep_step_of_cellTurn₁`.  If
there is one along `G₂` with `y ∉ Ḡ₁`, use `witnessStep_step_of_cellTurn₂`, which uses the step 1
label `hlab`.

LOUD: the residual is logically equivalent to the target, given this reduction.  It is strictly
smaller only in proof content.  See `WitnessCurveStepStatement.lean`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Lane gl-p07-40: the witness step residual from the residual off the cell turns.** -/
theorem witnessCurveSublistStep_of_witnessStepResidual
    (h : WitnessStepResidualStatement.{u, w, v}) :
    WitnessCurveSublistStepStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      hlab with hfwd | hbwd
  · refine Or.inl fun n s t x y hr => ?_
    by_cases hturn : WitnessStepCellTurn G₁ G₂ outerWalk y
    · unfold WitnessStepCellTurn at hturn
      rcases hturn with ⟨p, q, g, hg, hG⟩ | ⟨p, q, g, hg, hG, hy1⟩
      · exact witnessStep_step_of_cellTurn₁ E hr hG hg
      · exact witnessStep_step_of_cellTurn₂ E hlab hr hG hg hy1
    · exact hfwd n s t x y hr hturn
  · exact Or.inr hbwd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessCurveSublistStep_of_witnessStepResidual

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
