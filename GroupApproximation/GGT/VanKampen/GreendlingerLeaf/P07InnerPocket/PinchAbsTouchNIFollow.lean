import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchNIStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchNIArc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsFolParts
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-76: the NoInterleave and arc halves give the follows half

* `pinchAbsTouchNI_followPart_of`: `pinchAbsTouchNI_NIStatement` (this lane's target) and
  `pinchAbsTouchNI_ArcStatement` (lane gl-p07-77's clauses) give lane gl-p07-79's
  `pinchAbsFol_FollowPart`.  It always takes the second disjunct, `pinchAbsTouch_Tail`.  The circuit
  is the one from `pinchAbsTouch_exists_side`, and the tail is `pinchAbsTouchNI_tail_of`.
* `pinchAbsTouchNI_follow_of_blocks`: the same, from the block residual
  `pinchAbsTouchNI_Statement` (via `pinchAbsTouchNI_ni_of_statement`).

Neither uses `pinchAbsSub_OutsideStatement`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The two halves of the touch tail give the follows half.** -/
theorem pinchAbsTouchNI_followPart_of (hNI : pinchAbsTouchNI_NIStatement.{u, w, v})
    (hArc : pinchAbsTouchNI_ArcStatement.{u, w, v}) : pinchAbsFol_FollowPart.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hfo hout hinner houter C hC hCf hCa hCb hcase hP
  obtain ⟨comp, hside⟩ := pinchAbsTouch_exists_side (a := a) (b := b) (K := K) (G₁ := G₁)
    (G₂ := G₂) (f := C.face) hCf hout
  refine Or.inr ⟨comp, hside, fun henc => pinchAbsTouchNI_tail_of ?_ ?_⟩
  · exact hNI D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hfo hout
      hinner houter C hC hCf hCa hCb hcase hP comp hside henc
  · exact hArc D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hfo hout
      hinner houter C hC hCf hCa hCb hcase hP comp hside henc

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchNI_followPart_of

/-- **The block residual and the arc half give the follows half.** -/
theorem pinchAbsTouchNI_follow_of_blocks (h : pinchAbsTouchNI_Statement.{u, w, v})
    (hArc : pinchAbsTouchNI_ArcStatement.{u, w, v}) : pinchAbsFol_FollowPart.{u, w, v} :=
  pinchAbsTouchNI_followPart_of (pinchAbsTouchNI_ni_of_statement h) hArc

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchNI_follow_of_blocks

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
