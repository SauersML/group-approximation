import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NoninterleaveList
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-24: four noninterleaving facts from a four-block reading

This is the list layer of lane gl-p07-24.  The lane's mathematics is in
`FourPieceWitnessNoninterleaveStatement.lean`.  The context is Osin, arXiv:math/0411039v3, §9,
proof of Lemma 9.7(b).  This module certifies no printed sentence on its own.

## Statement

`FourPieceWitness.fourNoninterleave_of_blocks`: take three predicates `P1`, `P2`, `Pb` on the
entries of a list `l`.  Suppose a rotation of `l` reads `U₁ ++ U₂ ++ U₃ ++ U₄`, where:
* `U₁` lies in `P1`, and `U₃` lies in `¬P1 ∧ P2`;
* `U₂` and `U₄` lie in `¬P1 ∧ ¬P2`;
* `Pb` holds on all of `U₂` and fails on all of `U₄`, or the other way round.

Then `l` does not interleave in any of the four classes `P1`, `¬P1 ∧ P2`, `P1 ∨ (¬P2 ∧ Pb)` and
`P1 ∨ (¬P2 ∧ ¬Pb)`.

This is the list argument of `pocketLabelNoninterleaving_of_fourBlock`
(`NoninterleaveEndpoint.lean`), abstracted from the walk.  That theorem proves it inline for the
lake-fill walk only, so it cannot be reused for another walk.

## Proof

Apply `FourPiece.cyclicNoInterleave_of_four_blocks`.  It needs the first block inside the class,
the third block outside, and the other two blocks uniform.
* **`P1`.**  Blocks `U₁, U₂, U₃, U₄`.
* **`¬P1 ∧ P2`.**  Rotate to `U₃, U₄, U₁, U₂` (`FourPiece.rotate_four_mid`).
* **`P1 ∨ (¬P2 ∧ Pb)`, `P1 ∨ (¬P2 ∧ ¬Pb)`.**  Blocks `U₁, U₂, U₃, U₄`.  On `U₂` and `U₄` the class
  is `Pb` (or `¬Pb`), which the orientation clause makes uniform.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

namespace FourPieceWitness

section Lists

variable {α : Type*}

/-- **Four noninterleaving facts from a four-block reading.**  See the module docstring. -/
theorem fourNoninterleave_of_blocks {P1 P2 Pb : α → Prop} {l U₁ U₂ U₃ U₄ : List α} {n : ℕ}
    (hrot : l.rotate n = U₁ ++ U₂ ++ U₃ ++ U₄) (hU₁ : ∀ e ∈ U₁, P1 e)
    (hU₃ : ∀ e ∈ U₃, ¬ P1 e ∧ P2 e) (hU₂ : ∀ e ∈ U₂, ¬ P1 e ∧ ¬ P2 e)
    (hU₄ : ∀ e ∈ U₄, ¬ P1 e ∧ ¬ P2 e)
    (hor : ((∀ e ∈ U₂, Pb e) ∧ ∀ e ∈ U₄, ¬ Pb e) ∨ ((∀ e ∈ U₂, ¬ Pb e) ∧ ∀ e ∈ U₄, Pb e)) :
    FourPiece.CyclicNoInterleave P1 l ∧
      FourPiece.CyclicNoInterleave (fun e => ¬ P1 e ∧ P2 e) l ∧
      FourPiece.CyclicNoInterleave (fun e => P1 e ∨ (¬ P2 e ∧ Pb e)) l ∧
      FourPiece.CyclicNoInterleave (fun e => P1 e ∨ (¬ P2 e ∧ ¬ Pb e)) l := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact FourPiece.cyclicNoInterleave_of_four_blocks (A := P1) hrot hU₁
      (fun e he => (hU₃ e he).1) (Or.inr fun e he => (hU₂ e he).1)
      (Or.inr fun e he => (hU₄ e he).1)
  · exact FourPiece.cyclicNoInterleave_of_four_blocks (A := fun e => ¬ P1 e ∧ P2 e)
      (FourPiece.rotate_four_mid hrot) hU₃
      (fun e he hc => hc.1 (hU₁ e he)) (Or.inr fun e he hc => (hU₄ e he).2 hc.2)
      (Or.inr fun e he hc => (hU₂ e he).2 hc.2)
  · have h₃ : ∀ e ∈ U₃, ¬ (P1 e ∨ (¬ P2 e ∧ Pb e)) := by
      intro e he hc
      rcases hc with hc | hc
      · exact (hU₃ e he).1 hc
      · exact hc.1 (hU₃ e he).2
    rcases hor with ⟨hb₂, hb₄⟩ | ⟨hb₂, hb₄⟩
    · refine FourPiece.cyclicNoInterleave_of_four_blocks (A := fun e => P1 e ∨ (¬ P2 e ∧ Pb e))
        hrot (fun e he => Or.inl (hU₁ e he)) h₃
        (Or.inl fun e he => Or.inr ⟨(hU₂ e he).2, hb₂ e he⟩) (Or.inr fun e he hc => ?_)
      rcases hc with hc | hc
      · exact (hU₄ e he).1 hc
      · exact hb₄ e he hc.2
    · refine FourPiece.cyclicNoInterleave_of_four_blocks (A := fun e => P1 e ∨ (¬ P2 e ∧ Pb e))
        hrot (fun e he => Or.inl (hU₁ e he)) h₃
        (Or.inr fun e he hc => ?_) (Or.inl fun e he => Or.inr ⟨(hU₄ e he).2, hb₄ e he⟩)
      rcases hc with hc | hc
      · exact (hU₂ e he).1 hc
      · exact hb₂ e he hc.2
  · have h₃ : ∀ e ∈ U₃, ¬ (P1 e ∨ (¬ P2 e ∧ ¬ Pb e)) := by
      intro e he hc
      rcases hc with hc | hc
      · exact (hU₃ e he).1 hc
      · exact hc.1 (hU₃ e he).2
    rcases hor with ⟨hb₂, hb₄⟩ | ⟨hb₂, hb₄⟩
    · refine FourPiece.cyclicNoInterleave_of_four_blocks
        (A := fun e => P1 e ∨ (¬ P2 e ∧ ¬ Pb e))
        hrot (fun e he => Or.inl (hU₁ e he)) h₃
        (Or.inr fun e he hc => ?_) (Or.inl fun e he => Or.inr ⟨(hU₄ e he).2, hb₄ e he⟩)
      rcases hc with hc | hc
      · exact (hU₂ e he).1 hc
      · exact hc.2 (hb₂ e he)
    · refine FourPiece.cyclicNoInterleave_of_four_blocks
        (A := fun e => P1 e ∨ (¬ P2 e ∧ ¬ Pb e))
        hrot (fun e he => Or.inl (hU₁ e he)) h₃
        (Or.inl fun e he => Or.inr ⟨(hU₂ e he).2, hb₂ e he⟩) (Or.inr fun e he hc => ?_)
      rcases hc with hc | hc
      · exact (hU₄ e he).1 hc
      · exact hc.2 (hb₄ e he)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.fourNoninterleave_of_blocks

end Lists

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
