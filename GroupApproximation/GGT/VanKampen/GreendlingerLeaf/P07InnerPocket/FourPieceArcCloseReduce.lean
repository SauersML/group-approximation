import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcCloseStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcCloseArc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcAuditInside
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-26: the corrected residual from local step clauses

`arcAuditResidual_of_arcCloseStep` derives `PocketFourPieceArcAuditResidualStatement`
(`FourPieceArcAuditStatement.lean`) from the remaining gap `PocketFourPieceArcCloseStepStatement`
(`FourPieceArcCloseStatement.lean`).  `pocketFourPieceInside_of_arcCloseStep` then gives
`PocketFourPieceInsideStatement` through `pocketFourPieceInside_of_arcAuditResidual`.

## Proof route

* **Branch 2** is passed through unchanged.
* **Branch 1**: clauses 1, 2' and the four no-interleave clauses are passed through unchanged.
  * Clause 4a: an off-`G₁` entry of the complement `V` gives an off-`G₁` walk dart
    (`ArcClose.exists_not_mem_of_block`).  So S1a applies, and `ArcClose.arc_of_block` extracts
    the arc.
  * Clause 4b: an all-`G₁` inverse walk is an all-`G₁` walk (`ArcClose.all_mem_of_invDarts`).
    So S1b applies, and `ArcClose.arc_of_all` rotates past the unique junction.
  * The same for `G₂/j`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Lane gl-p07-26: the corrected residual from local step clauses.** -/
theorem arcAuditResidual_of_arcCloseStep
    (h : PocketFourPieceArcCloseStepStatement.{u, w, v}) :
    PocketFourPieceArcAuditResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw
    hout hinner houter C hC hCf hCa hCb
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
      houter C hC hCf hCa hCb with
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

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.arcAuditResidual_of_arcCloseStep

/-- **Lane gl-p07-26: the reading part from the local step clauses.** -/
theorem pocketFourPieceInside_of_arcCloseStep
    (h : PocketFourPieceArcCloseStepStatement.{u, w, v}) :
    PocketFourPieceInsideStatement.{u, w, v} :=
  pocketFourPieceInside_of_arcAuditResidual (arcAuditResidual_of_arcCloseStep h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketFourPieceInside_of_arcCloseStep

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
