import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchNIParts
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NoninterleaveList
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-76: the block reading gives the four NoInterleave facts

* `pinchAbsTouchNI_list_of_blocks`: the list layer, for arbitrary predicates `P₁`, `P₂`, `Pb`
  on an arbitrary type.
* `pinchAbsTouchNI_niPart_of_blocks : pinchAbsTouchNI_Blocks → pinchAbsTouchNI_NIPart`.

## Proof

It is the proof of lane gl-p07-17's `pocketLabelNoninterleaving_of_fourBlock`
(`NoninterleaveEndpoint.lean`), made generic.  A rotation of `l` is `U₁ ++ U₂ ++ U₃ ++ U₄`.
Each case applies `FourPiece.cyclicNoInterleave_of_four_blocks`:
* **`P₁`.**  `U₁` is inside, and the other three blocks are outside.
* **`¬P₁ ∧ P₂`.**  Rotate to `U₃ ++ U₄ ++ U₁ ++ U₂` (`FourPiece.rotate_four_mid`).  Then `U₃` is
  inside, and the other three blocks are outside.
* **`P₁ ∨ (¬P₂ ∧ Pb)` and `P₁ ∨ (¬P₂ ∧ ¬Pb)`.**  `U₁` is inside and `U₃` is outside.  On `U₂`
  and `U₄` the class is `Pb` (or `¬Pb`), which the orientation clause makes uniform.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The list layer.**  Four blocks in the orientation of `pinchAbsTouchNI_Blocks` give the
four NoInterleave facts, for arbitrary predicates. -/
theorem pinchAbsTouchNI_list_of_blocks {α : Type*} {P₁ P₂ Pb : α → Prop}
    {l U₁ U₂ U₃ U₄ : List α} {n : ℕ} (hrot : l.rotate n = U₁ ++ U₂ ++ U₃ ++ U₄)
    (hU₁ : ∀ e ∈ U₁, P₁ e) (hU₃ : ∀ e ∈ U₃, ¬ P₁ e ∧ P₂ e)
    (hU₂ : ∀ e ∈ U₂, ¬ P₁ e ∧ ¬ P₂ e) (hU₄ : ∀ e ∈ U₄, ¬ P₁ e ∧ ¬ P₂ e)
    (hor : ((∀ e ∈ U₂, Pb e) ∧ ∀ e ∈ U₄, ¬ Pb e) ∨
      ((∀ e ∈ U₂, ¬ Pb e) ∧ ∀ e ∈ U₄, Pb e)) :
    FourPiece.CyclicNoInterleave P₁ l ∧
      FourPiece.CyclicNoInterleave (fun e => ¬ P₁ e ∧ P₂ e) l ∧
      FourPiece.CyclicNoInterleave (fun e => P₁ e ∨ (¬ P₂ e ∧ Pb e)) l ∧
      FourPiece.CyclicNoInterleave (fun e => P₁ e ∨ (¬ P₂ e ∧ ¬ Pb e)) l := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact FourPiece.cyclicNoInterleave_of_four_blocks hrot hU₁ (fun e he => (hU₃ e he).1)
      (Or.inr fun e he => (hU₂ e he).1) (Or.inr fun e he => (hU₄ e he).1)
  · exact FourPiece.cyclicNoInterleave_of_four_blocks (FourPiece.rotate_four_mid hrot) hU₃
      (fun e he hc => hc.1 (hU₁ e he)) (Or.inr fun e he hc => (hU₄ e he).2 hc.2)
      (Or.inr fun e he hc => (hU₂ e he).2 hc.2)
  · have h₃ : ∀ e ∈ U₃, ¬ (P₁ e ∨ (¬ P₂ e ∧ Pb e)) := by
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
  · have h₃ : ∀ e ∈ U₃, ¬ (P₁ e ∨ (¬ P₂ e ∧ ¬ Pb e)) := by
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

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchNI_list_of_blocks

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The block reading gives the NoInterleave part.**  List combinatorics only. -/
theorem pinchAbsTouchNI_niPart_of_blocks {b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {outerWalk : List X.toCombMap.Dart} (h : pinchAbsTouchNI_Blocks b G₁ G₂ outerWalk) :
    pinchAbsTouchNI_NIPart b G₁ G₂ outerWalk := by
  obtain ⟨n, U₁, U₂, U₃, U₄, hrot, hU₁, hU₃, hU₂, hU₄, hor⟩ := h
  exact pinchAbsTouchNI_list_of_blocks (P₁ := fun e => e ∈ invDarts X G₁.darts)
    (P₂ := fun e => e ∈ invDarts X G₂.darts) (Pb := fun e => X.toCombMap.alpha e ∈ b.sideFrom i)
    hrot hU₁ hU₃ hU₂ hU₄ hor

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchNI_niPart_of_blocks

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
