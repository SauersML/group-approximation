import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NoPlanarDegenStepStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcCloseArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-33: the no-walk residual from local step clauses

`FourPieceWitness.noPlanarDegenerate_of_step` derives lane 28's
`FourPieceWitness.NoPlanarDegenerateStatement` from `FourPieceWitness.NoPlanarDegenStepStatement`
(`NoPlanarDegenStepStatement.lean`).

## Proof route

* The extra connectivity hypothesis is `not_connected_of_not_exists_walk hout hCf hno`.
* **Branch 2** is passed through unchanged.
* **Branch 1**: clauses 1, 2' and the four no-interleave clauses are passed through unchanged.
  * Clause 4a: an off-`G₁` complement entry gives an off-`G₁` walk dart
    (`ArcClose.exists_not_mem_of_block`).  So S1a applies, and `ArcClose.arc_of_block` extracts
    the arc.
  * Clause 4b: an all-`G₁` inverse walk is an all-`G₁` walk (`ArcClose.all_mem_of_invDarts`).  So
    S1b applies, and `ArcClose.arc_of_all` rotates past the unique junction.
  * The same for `G₂/j`.

This is the proof of `arcAuditResidual_of_arcCloseStep` (lane 26), under the no-walk hypothesis.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Lane gl-p07-33: the no-walk residual from local step clauses.** -/
theorem noPlanarDegenerate_of_step (h : NoPlanarDegenStepStatement.{u, w, v}) :
    NoPlanarDegenerateStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw
    hout hinner houter C hC hCf hCa hCb hno
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
      houter C hC hCf hCa hCb hno (not_connected_of_not_exists_walk hout hCf hno) with
    ⟨faces, outerWalk, E, hCF, hsub, hdart, hn1, hn2, hnb, hna, hs₁, hu₁, hs₂, hu₂⟩ | hbr
  · refine Or.inl ⟨faces, outerWalk, E, hCF, hsub, hdart, hn1, hn2, hnb, hna, ?_, ?_, ?_, ?_⟩
    · intro m U V hm hU hV
      exact ArcClose.arc_of_block E i G₁ (hs₁ (ArcClose.exists_not_mem_of_block G₁ hm hV)) hm hU
    · intro hall
      exact ArcClose.arc_of_all E i G₁ (ArcClose.all_mem_of_invDarts G₁ hall)
        (hu₁ (ArcClose.all_mem_of_invDarts G₁ hall))
    · intro m U V hm hU hV
      exact ArcClose.arc_of_block E j G₂ (hs₂ (ArcClose.exists_not_mem_of_block G₂ hm hV)) hm hU
    · intro hall
      exact ArcClose.arc_of_all E j G₂ (ArcClose.all_mem_of_invDarts G₂ hall)
        (hu₂ (ArcClose.all_mem_of_invDarts G₂ hall))
  · exact Or.inr hbr

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.noPlanarDegenerate_of_step

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
