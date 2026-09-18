import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlockNondegStepStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlockList
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-32: the nondegenerate four-block reading from the curve

Lane gl-p07-32.  This file proves `FourPieceWitness.FourBlockNondegLabelStatement`
(`FourBlockWitnessLabel.lean`) and `FourPieceWitness.FourBlockNondegStatement`
(`FourBlockWitnessAudit.lean`) from `FourPieceWitness.WitnessCurveSublistNondegStatement`
(`FourBlockNondegStepStatement.lean`).  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).
Certifies no printed sentence on its own.

* **Forward reading.**  The rotation `r` is a sublist of `Ḡ₁ ++ Ā' ++ Ḡ₂' ++ B̄'`, where the primes
  mark the priority-filtered words.  Split `r` into four blocks
  (`FourBlock.exists_blocks_of_sublist`) and read the classes off the words.  `U₂` is in class `A`
  and `U₄` in class `B`: the second disjunct.
* **Reverse reading.**  `r.reverse` is such a sublist.  A further rotation `r.rotate k` reads
  `Ḡ₁`, then `B̄'`, then `Ḡ₂'`, then `Ā'` (`FourBlock.exists_rotate_blocks_of_reverse_sublist`).
  Now `U₂` is in class `B` and `U₄` in class `A`: the first disjunct.  The rotations combine by
  `List.rotate_rotate`.
* **The unlabelled statement.**  `fourBlockNondeg_of_label` supplies the step 1 label.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Lane gl-p07-32: the labelled nondegenerate four-block reading from the curve residual.** -/
theorem fourBlockNondegLabel_of_curveSublist (h : WitnessCurveSublistNondegStatement.{u, w, v}) :
    FourBlockNondegLabelStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  obtain ⟨n, hsub | hsub⟩ := h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  · obtain ⟨U₁, U₂, U₃, U₄, hl, hU₁, hU₂, hU₃, hU₄⟩ := FourBlock.exists_blocks_of_sublist hsub
    exact ⟨n, U₁, U₂, U₃, U₄, hl, hU₁, fun e he => FourBlock.mem_cellG2Word (hU₃ e he),
      fun e he => ⟨(FourBlock.mem_sideAWord (hU₂ e he)).1,
        (FourBlock.mem_sideAWord (hU₂ e he)).2.1⟩,
      fun e he => ⟨(FourBlock.mem_sideBWord (hU₄ e he)).1,
        (FourBlock.mem_sideBWord (hU₄ e he)).2.1⟩,
      Or.inr ⟨fun e he => (FourBlock.mem_sideAWord (hU₂ e he)).2.2,
        fun e he => (FourBlock.mem_sideBWord (hU₄ e he)).2.2⟩⟩
  · obtain ⟨k, U₁, U₂, U₃, U₄, hl, hU₁, hU₂, hU₃, hU₄⟩ :=
      FourBlock.exists_rotate_blocks_of_reverse_sublist hsub
    rw [List.rotate_rotate] at hl
    exact ⟨n + k, U₁, U₂, U₃, U₄, hl, hU₁, fun e he => FourBlock.mem_cellG2Word (hU₃ e he),
      fun e he => ⟨(FourBlock.mem_sideBWord (hU₂ e he)).1,
        (FourBlock.mem_sideBWord (hU₂ e he)).2.1⟩,
      fun e he => ⟨(FourBlock.mem_sideAWord (hU₄ e he)).1,
        (FourBlock.mem_sideAWord (hU₄ e he)).2.1⟩,
      Or.inl ⟨fun e he => (FourBlock.mem_sideBWord (hU₂ e he)).2.2,
        fun e he => (FourBlock.mem_sideAWord (hU₄ e he)).2.2⟩⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.fourBlockNondegLabel_of_curveSublist

/-- **Lane gl-p07-32: the nondegenerate four-block reading of the witness outside walk from the
curve residual.** -/
theorem fourBlockNondeg_of_curveSublist (h : WitnessCurveSublistNondegStatement.{u, w, v}) :
    FourBlockNondegStatement.{u, w, v} :=
  fourBlockNondeg_of_label (fourBlockNondegLabel_of_curveSublist h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.fourBlockNondeg_of_curveSublist

/-- **Lane gl-p07-32: the corrected noninterleave statement from the curve residual.** -/
theorem noninterleaveNondeg_of_curveSublist (h : WitnessCurveSublistNondegStatement.{u, w, v}) :
    NoninterleaveNondegStatement.{u, w, v} :=
  noninterleaveNondeg_of_fourBlockNondeg (fourBlockNondeg_of_curveSublist h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.noninterleaveNondeg_of_curveSublist

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
