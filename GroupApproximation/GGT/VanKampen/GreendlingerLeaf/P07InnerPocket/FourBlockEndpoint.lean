import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlockList
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlockStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-22: the four-block reading from the pocket curve

Lane gl-p07-22.  This file proves `PocketLabelFourBlockStatement` (`NoninterleaveStatement.lean`)
from `FourBlock.PocketCurveSublistStatement` (`FourBlockStatement.lean`).  Infrastructure for Osin,
arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Certifies no printed sentence on its own.

* **Forward reading.**  The rotation `r` is a sublist of `Ḡ₁ ++ Ā' ++ Ḡ₂' ++ B̄'`, where the primes
  mark the priority-filtered words.  Split `r` into four blocks (`exists_blocks_of_sublist`).  Read
  the classes off the words (`mem_sideAWord`, `mem_cellG2Word`, `mem_sideBWord`).  The gap `U₂` is
  in class `A` and `U₄` is in class `B`.
* **Reverse reading.**  `r.reverse` is such a sublist.  A further rotation `r.rotate k` reads
  `Ḡ₁`-entries, then `B̄'`, then `Ḡ₂'`, then `Ā'` (`exists_rotate_blocks_of_reverse_sublist`).  Now
  `U₂` is in class `B` and `U₄` is in class `A`.  The rotations combine by `List.rotate_rotate`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse
  Surgery.MapCollapse.ExteriorComponent
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill

/-- **Lane gl-p07-22: the four-block reading of the pocket outer walk, from the pocket curve
residual.** -/
theorem pocketLabelFourBlock_of_curveSublist (h : PocketCurveSublistStatement.{u, w, v}) :
    PocketLabelFourBlockStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ h₁ G₂ h₂ hw
    hoff hinner houter C hC hCf hCa hCb L hL outerWalk E hmem
  obtain ⟨n, hsub | hsub⟩ := h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ h₁ G₂ h₂
    hw hoff hinner houter C hC hCf hCa hCb L hL outerWalk E hmem
  · obtain ⟨U₁, U₂, U₃, U₄, hl, hU₁, hU₂, hU₃, hU₄⟩ := exists_blocks_of_sublist hsub
    exact ⟨n, U₁, U₂, U₃, U₄, hl, hU₁, fun e he => mem_cellG2Word (hU₃ e he),
      fun e he => ⟨(mem_sideAWord (hU₂ e he)).1, (mem_sideAWord (hU₂ e he)).2.1⟩,
      fun e he => ⟨(mem_sideBWord (hU₄ e he)).1, (mem_sideBWord (hU₄ e he)).2.1⟩,
      Or.inr ⟨fun e he => (mem_sideAWord (hU₂ e he)).2.2,
        fun e he => (mem_sideBWord (hU₄ e he)).2.2⟩⟩
  · obtain ⟨k, U₁, U₂, U₃, U₄, hl, hU₁, hU₂, hU₃, hU₄⟩ :=
      exists_rotate_blocks_of_reverse_sublist hsub
    rw [List.rotate_rotate] at hl
    exact ⟨n + k, U₁, U₂, U₃, U₄, hl, hU₁, fun e he => mem_cellG2Word (hU₃ e he),
      fun e he => ⟨(mem_sideBWord (hU₂ e he)).1, (mem_sideBWord (hU₂ e he)).2.1⟩,
      fun e he => ⟨(mem_sideAWord (hU₄ e he)).1, (mem_sideAWord (hU₄ e he)).2.1⟩,
      Or.inl ⟨fun e he => (mem_sideBWord (hU₂ e he)).2.2,
        fun e he => (mem_sideAWord (hU₄ e he)).2.2⟩⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock.pocketLabelFourBlock_of_curveSublist

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock
