import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NoninterleaveList
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NoninterleaveStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-17: noninterleaving from the four-block reading

This file proves `PocketLabelNoninterleavingStatement` (`FourPieceOrder.lean`) from the residual
`PocketLabelFourBlockStatement` (`NoninterleaveStatement.lean`), whose docstring has the truth
check.

## Proof

The residual gives `(invDarts X outerWalk).rotate n = U₁ ++ U₂ ++ U₃ ++ U₄`.  Write
`P1 e := e ∈ invDarts G₁`, `P2 e := e ∈ invDarts G₂` and `Pb e := α e ∈ b.sideFrom i`.  Apply
`FourPiece.cyclicNoInterleave_of_four_blocks`, which needs its first block inside the class, its
third block outside, and its other two blocks uniform:
* **`P1`.**  Blocks `U₁, U₂, U₃, U₄`: `U₁` is inside, and the other three are outside.
* **`¬P1 ∧ P2`.**  Rotate by `|U₁ ++ U₂|` to `U₃, U₄, U₁, U₂` (`FourPiece.rotate_four_mid`).
  `U₃` is inside, and the other three are outside.
* **`P1 ∨ (¬P2 ∧ Pb)`.**  Blocks `U₁, U₂, U₃, U₄`: `U₁` is inside and `U₃` is outside (`P1` and `P2`
  fail on `U₃`).  On `U₂` and `U₄` the class is `Pb`, which the orientation clause makes uniform.
* **`P1 ∨ (¬P2 ∧ ¬Pb)`.**  The same, with `¬Pb`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse
  Surgery.MapCollapse.ExteriorComponent
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill

/-- **Lane gl-p07-17, reduced to the four-block reading.**  The four noninterleaving facts follow
from the blockwise reading of the pocket curve by list combinatorics only. -/
theorem pocketLabelNoninterleaving_of_fourBlock
    (h : PocketLabelFourBlockStatement.{u, w, v}) :
    PocketLabelNoninterleavingStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ h₁ G₂ h₂ hw
    hoff hinner houter C hC hCf hCa hCb L hL outerWalk E hmem
  obtain ⟨n, U₁, U₂, U₃, U₄, hrot, hU₁, hU₃, hU₂, hU₄, hor⟩ := h D eps X a b K hij hai hbi hab
    hlabel hW hfirst hsecond G₁ h₁ G₂ h₂ hw hoff hinner houter C hC hCf hCa hCb L hL outerWalk E
    hmem
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine FourPiece.cyclicNoInterleave_of_four_blocks hrot hU₁ (fun e he => (hU₃ e he).1)
      (Or.inr fun e he => (hU₂ e he).1) (Or.inr fun e he => (hU₄ e he).1)
  · refine FourPiece.cyclicNoInterleave_of_four_blocks (FourPiece.rotate_four_mid hrot) hU₃
      (fun e he hc => hc.1 (hU₁ e he)) (Or.inr fun e he hc => (hU₄ e he).2 hc.2)
      (Or.inr fun e he hc => (hU₂ e he).2 hc.2)
  · have h₃ : ∀ e ∈ U₃, ¬ (e ∈ invDarts X G₁.darts ∨
        (e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∈ b.sideFrom i)) := by
      intro e he hc
      rcases hc with hc | hc
      · exact (hU₃ e he).1 hc
      · exact hc.1 (hU₃ e he).2
    rcases hor with ⟨hb₂, hb₄⟩ | ⟨hb₂, hb₄⟩
    · refine FourPiece.cyclicNoInterleave_of_four_blocks hrot (fun e he => Or.inl (hU₁ e he)) h₃
        (Or.inl fun e he => Or.inr ⟨(hU₂ e he).2, hb₂ e he⟩) (Or.inr fun e he hc => ?_)
      rcases hc with hc | hc
      · exact (hU₄ e he).1 hc
      · exact hb₄ e he hc.2
    · refine FourPiece.cyclicNoInterleave_of_four_blocks hrot (fun e he => Or.inl (hU₁ e he)) h₃
        (Or.inr fun e he hc => ?_) (Or.inl fun e he => Or.inr ⟨(hU₄ e he).2, hb₄ e he⟩)
      rcases hc with hc | hc
      · exact (hU₂ e he).1 hc
      · exact hb₂ e he hc.2
  · have h₃ : ∀ e ∈ U₃, ¬ (e ∈ invDarts X G₁.darts ∨
        (e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∉ b.sideFrom i)) := by
      intro e he hc
      rcases hc with hc | hc
      · exact (hU₃ e he).1 hc
      · exact hc.1 (hU₃ e he).2
    rcases hor with ⟨hb₂, hb₄⟩ | ⟨hb₂, hb₄⟩
    · refine FourPiece.cyclicNoInterleave_of_four_blocks hrot (fun e he => Or.inl (hU₁ e he)) h₃
        (Or.inr fun e he hc => ?_) (Or.inl fun e he => Or.inr ⟨(hU₄ e he).2, hb₄ e he⟩)
      rcases hc with hc | hc
      · exact (hU₂ e he).1 hc
      · exact hc.2 (hb₂ e he)
    · refine FourPiece.cyclicNoInterleave_of_four_blocks hrot (fun e he => Or.inl (hU₁ e he)) h₃
        (Or.inl fun e he => Or.inr ⟨(hU₂ e he).2, hb₂ e he⟩) (Or.inr fun e he hc => ?_)
      rcases hc with hc | hc
      · exact (hU₄ e he).1 hc
      · exact hc.2 (hb₄ e he)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketLabelNoninterleaving_of_fourBlock

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
