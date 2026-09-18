import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessArcsBlocksStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessArcsBlocksLocal
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcsAuditPinchStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-44: proof of the block-local clause 4

* `witnessArcsBlocks` proves `WitnessArcsBlocksStatement` (`WitnessArcsBlocksStatement.lean`).
  - Clauses 4a are `witnessArcsBlocks_arc_of_block` for `(i, G₁)` and `(j, G₂)`.
  - Clauses 4b are `witnessArcsBlocks_arc_of_all` for `(i, G₁)` and `(j, G₂)`.
  - Neither uses the pocket premises.  Clause 4 at the witness level is a statement about
    successor walks only.
* `witnessArcsBlocks_arcsAuditPinch` recovers the proved `FourPieceWitness.ArcsAuditPinchStatement`
  (lane gl-p07-29) from this statement.  So this statement is at least as strong.
  - 4a: a pinch-free `G₁` makes every non-final block dart good.  The block entry lies on `G₁`
    by `witnessArcsBlocks_mem_of_dropLast`.  The complement hypothesis is dropped.
  - 4b: a bad walk dart is a pinched dart of `G₁` (`ArcClose.all_mem_of_invDarts`).  So the
    `G₁` pinch bound bounds the bad walk darts.

The target `PocketFourPieceWitnessArcsStatement` is FALSE (model M2).  See the Statement file.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Lane gl-p07-44: the block-local clause 4 for the cut-down witness holds.** -/
theorem witnessArcsBlocks : WitnessArcsBlocksStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  exact ⟨fun _ _ _ hm hU hloc => witnessArcsBlocks_arc_of_block E i G₁ hm hU hloc,
    fun hall hone => witnessArcsBlocks_arc_of_all E i G₁ hall hone,
    fun _ _ _ hm hU hloc => witnessArcsBlocks_arc_of_block E j G₂ hm hU hloc,
    fun hall hone => witnessArcsBlocks_arc_of_all E j G₂ hall hone⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessArcsBlocks

/-- **The block-local statement recovers the pinch-bounded arc audit.** -/
theorem witnessArcsBlocks_arcsAuditPinch (h : WitnessArcsBlocksStatement.{u, w, v}) :
    FourPieceWitness.ArcsAuditPinchStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  obtain ⟨h4a₁, h4b₁, h4a₂, h4b₂⟩ := h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond
    G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  refine ⟨fun hpf m U V hm hU _ => h4a₁ m U V hm hU fun x hx =>
      Or.inr (hpf x (witnessArcsBlocks_mem_of_dropLast G₁ hU hx)),
    fun hone hall => h4b₁ hall fun x hx y hy hnx hny =>
      hone x (ArcClose.all_mem_of_invDarts G₁ hall x hx) y
        (ArcClose.all_mem_of_invDarts G₁ hall y hy)
        (fun hp => hnx (Or.inr hp)) (fun hp => hny (Or.inr hp)),
    fun hpf m U V hm hU _ => h4a₂ m U V hm hU fun x hx =>
      Or.inr (hpf x (witnessArcsBlocks_mem_of_dropLast G₂ hU hx)),
    fun hone hall => h4b₂ hall fun x hx y hy hnx hny =>
      hone x (ArcClose.all_mem_of_invDarts G₂ hall x hx) y
        (ArcClose.all_mem_of_invDarts G₂ hall y hy)
        (fun hp => hnx (Or.inr hp)) (fun hp => hny (Or.inr hp))⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessArcsBlocks_arcsAuditPinch

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
