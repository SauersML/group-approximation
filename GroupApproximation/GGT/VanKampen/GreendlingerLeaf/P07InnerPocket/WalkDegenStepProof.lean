import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WalkDegenStepStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCaseProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcCloseArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-37c: the walk-degenerate residual from local step clauses

`PinchCase.walkDegen_of_step` derives lane 34's `PinchCase.WalkDegenStatement` from
`PinchCase.WalkDegenStepStatement` (`WalkDegenStepStatement.lean`).

## Proof route

* **Branch 2** is passed through unchanged.
* **Branch 1**: clauses 1, 2' and the four no-interleave clauses are passed through unchanged.
  * Clause 4a: an off-`G₁` complement entry gives an off-`G₁` walk dart
    (`ArcClose.exists_not_mem_of_block`).  So S1a applies, and `ArcClose.arc_of_block` extracts
    the arc.
  * Clause 4b: an all-`G₁` inverse walk is an all-`G₁` walk (`ArcClose.all_mem_of_invDarts`).  So
    S1b applies, and `ArcClose.arc_of_all` rotates past the unique junction.
  * The same for `G₂/j`.

This is the proof of `FourPieceWitness.noPlanarDegenerate_of_step` (lane 33), under the witness-walk
premise block of lane 34.

`PinchCase.walkDegen_pocketFourPieceOff_of_step` is the end-to-end
consumer.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Lane gl-p07-37c: the walk-degenerate residual from local step clauses.** -/
theorem walkDegen_of_step (h : WalkDegenStepStatement.{u, w, v}) :
    WalkDegenStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hnd hbad
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
      houter C hC hCf hCa hCb outerWalk E hnb hnd hbad with
    ⟨faces, ow, E', hCF, hsub, hdart, hn1, hn2, hn3, hn4, hs₁, hu₁, hs₂, hu₂⟩ | hbr
  · refine Or.inl ⟨faces, ow, E', hCF, hsub, hdart, hn1, hn2, hn3, hn4, ?_, ?_, ?_, ?_⟩
    · intro m U V hm hU hV
      exact ArcClose.arc_of_block E' i G₁ (hs₁ (ArcClose.exists_not_mem_of_block G₁ hm hV)) hm hU
    · intro hall
      exact ArcClose.arc_of_all E' i G₁ (ArcClose.all_mem_of_invDarts G₁ hall)
        (hu₁ (ArcClose.all_mem_of_invDarts G₁ hall))
    · intro m U V hm hU hV
      exact ArcClose.arc_of_block E' j G₂ (hs₂ (ArcClose.exists_not_mem_of_block G₂ hm hV)) hm hU
    · intro hall
      exact ArcClose.arc_of_all E' j G₂ (ArcClose.all_mem_of_invDarts G₂ hall)
        (hu₂ (ArcClose.all_mem_of_invDarts G₂ hall))
  · exact Or.inr hbr

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.walkDegen_of_step

/-- **`PocketFourPieceOffStatement` through the step-form gaps**: gl-p07-32's
`WitnessCurveSublistNondegStatement` for (read), gl-p07-33's `NoPlanarDegenStepStatement` for
the no-walk case, and this lane's `WalkDegenStepStatement` for the walk-degenerate case. -/
theorem walkDegen_pocketFourPieceOff_of_step
    (hcurve : FourPieceWitness.WitnessCurveSublistNondegStatement.{u, w, v})
    (hstep : FourPieceWitness.NoPlanarDegenStepStatement.{u, w, v})
    (hwalk : WalkDegenStepStatement.{u, w, v}) : PocketFourPieceOffStatement.{u, w, v} :=
  pocketFourPieceOff_of_curveSublist_noPlanarDegenStep_walkDegen hcurve hstep
    (walkDegen_of_step hwalk)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.walkDegen_pocketFourPieceOff_of_step

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase
