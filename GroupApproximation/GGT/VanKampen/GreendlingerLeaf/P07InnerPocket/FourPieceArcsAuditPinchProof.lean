import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcsAuditPinchStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcCloseArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-29: proof of the pinch-bounded arc audit

This file proves `FourPieceWitness.ArcsAuditPinchStatement`
(`FourPieceArcsAuditPinchStatement.lean`).  The uncorrected `ArcsAuditStatement` is false (model M11 there).

## Proof route

Let `E : EnclosedFaceSetSucc X F outerWalk` with `F = witnessFaces a b K C.face`.
* **4a.**  Every dart of `G₁` is pinch-free.  So at each position `p` where `outerWalk[p]` lies on
  `G₁`, the local step clause of `ArcClose.arc_of_block` (lane gl-p07-26) holds by its second
  disjunct.
* **4b.**  `ArcClose.all_mem_of_invDarts` turns the hypothesis into "every walk dart lies on
  `G₁`".  Take two positions `p` and `q` that are neither kept nor pinch-free.  Their darts lie on
  `G₁` and are not pinch-free, so the pinch bound makes them equal.  `E.nodup` then gives `p = q`
  (`List.Nodup.getElem_inj_iff`), which is the junction clause of `ArcClose.arc_of_all`.
* The clauses for `G₂` and `Π_j` are proved the same way.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **The pinch-bounded arc audit holds.**  See the module docstring. -/
theorem arcsAuditPinch : ArcsAuditPinchStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  refine ⟨fun hpf m U V hm hU _ => ?_, fun hone hall => ?_,
    fun hpf m U V hm hU _ => ?_, fun hone hall => ?_⟩
  · exact ArcClose.arc_of_block E i G₁ (fun p _ h0 _ => Or.inr (hpf _ h0)) hm hU
  · have hmem := ArcClose.all_mem_of_invDarts G₁ hall
    exact ArcClose.arc_of_all E i G₁ hmem (fun p q hp hq hnp hnq =>
      (E.nodup.getElem_inj_iff).mp
        (hone _ (hmem _ (List.getElem_mem hp)) _ (hmem _ (List.getElem_mem hq))
          (fun h => hnp (Or.inr h)) (fun h => hnq (Or.inr h))))
  · exact ArcClose.arc_of_block E j G₂ (fun p _ h0 _ => Or.inr (hpf _ h0)) hm hU
  · have hmem := ArcClose.all_mem_of_invDarts G₂ hall
    exact ArcClose.arc_of_all E j G₂ hmem (fun p q hp hq hnp hnq =>
      (E.nodup.getElem_inj_iff).mp
        (hone _ (hmem _ (List.getElem_mem hp)) _ (hmem _ (List.getElem_mem hq))
          (fun h => hnp (Or.inr h)) (fun h => hnq (Or.inr h))))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.arcsAuditPinch

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
