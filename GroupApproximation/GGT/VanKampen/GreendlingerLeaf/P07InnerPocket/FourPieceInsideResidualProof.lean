import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceInsideResidualStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceInsideCloseProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcCloseArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-48: the lake-only residual from local step clauses

* `fourPieceInsideResidual_of_step`: `FourPieceInsideResidualStepStatement`
  (`FourPieceInsideResidualStatement.lean`) gives `FourPieceInsideCloseResidualStatement`.
* `fourPieceInsideResidual_inside_of_step`: it gives `PocketFourPieceInsideStatement`, through
  `fourPieceInsideClose_of_residual`.
* `fourPieceInsideResidual_step_of_arcCloseStep`: lane 26's gap
  `PocketFourPieceArcCloseStepStatement` gives the new statement, since clause 3 only gains a
  hypothesis.

## Proof route of `fourPieceInsideResidual_of_step`

* **Branch 2** is passed through unchanged.
* **Branch 1**: clauses 1, 2', the lake-only clause 3 and the four no-interleave clauses are passed
  through unchanged.
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

/-- **Lane gl-p07-48: the lake-only residual from local step clauses.** -/
theorem fourPieceInsideResidual_of_step
    (h : FourPieceInsideResidualStepStatement.{u, w, v}) :
    FourPieceInsideCloseResidualStatement.{u, w, v} := by
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

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.fourPieceInsideResidual_of_step

/-- **Lane gl-p07-48: the reading part from the lake-only local step clauses.** -/
theorem fourPieceInsideResidual_inside_of_step
    (h : FourPieceInsideResidualStepStatement.{u, w, v}) :
    PocketFourPieceInsideStatement.{u, w, v} :=
  fourPieceInsideClose_of_residual (fourPieceInsideResidual_of_step h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.fourPieceInsideResidual_inside_of_step

/-- **Lane 26's gap gives the lake-only step residual.**  Clause 3 only gains a hypothesis. -/
theorem fourPieceInsideResidual_step_of_arcCloseStep
    (h : PocketFourPieceArcCloseStepStatement.{u, w, v}) :
    FourPieceInsideResidualStepStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw
    hout hinner houter C hC hCf hCa hCb
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
      houter C hC hCf hCa hCb with
    ⟨faces, outerWalk, E, hCF, hsub, hrest⟩ | hbr
  · exact Or.inl ⟨faces, outerWalk, E, hCF, fun _ => hsub, hrest⟩
  · exact Or.inr hbr

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.fourPieceInsideResidual_step_of_arcCloseStep

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
