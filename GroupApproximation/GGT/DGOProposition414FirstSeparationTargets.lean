import GroupApproximation.GGT.DGOProposition414CycleBlocks

/-!
# The four classes of distinguished side of a Proposition 4.14 gap child

`FirstGapTargetSeparation` quantifies over the distinguished sides of one gap
child, and the argument that separates each of them from the other components
of the cycle depends on which of Dahmani--Guirardel--Osin's types it is: an
inherited arc target, a charged partner edge of the opposite half, or one of
the two connectors.  This module names that classification, in the explicit
index form the cut dictionary consumes.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- A canonical connector target is a left index or a shifted right index. -/
theorem mem_auxiliaryCycleConnectorTarget_cases
    (left right : List (RelLetter G Λ)) (nArc : ℕ) {s : ℕ}
    (hs : s ∈ auxiliaryCycleConnectorTarget left right nArc) :
    s < left.length ∨
      (∃ r : ℕ, r < right.length ∧ s = left.length + nArc + r) := by
  classical
  rw [auxiliaryCycleConnectorTarget, Finset.mem_union] at hs
  rcases hs with hs | hs
  · exact Or.inl (Finset.mem_range.mp hs)
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    exact Or.inr ⟨r, Finset.mem_range.mp hr, rfl⟩

namespace BalancedSplitData

/-- Every distinguished side of a first-half gap child is an inherited arc
target, a charged partner edge, a left connector letter or a right connector
letter. -/
theorem firstGapTarget_cases
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    {s : ℕ} (hs : s ∈ B.firstGapTarget j) :
    (∃ t ∈ B.firstGapArcSources j,
        s = (B.firstGapLeft j).length +
          (B.firstTargetSide t - B.firstGapStartSide j)) ∨
      (∃ t ∈ B.firstGapChordSources j,
        s = B.firstGapChordTargetIndex j
          (B.brokenAssignment.second.partner t)) ∨
      s < (B.firstGapLeft j).length ∨
      (∃ r : ℕ, r < (B.firstGapRight j).length ∧
        s = (B.firstGapLeft j).length +
          (B.firstGapFinishSide j - B.firstGapStartSide j) + r) := by
  classical
  simp only [firstGapTarget, firstGapLocalTarget, Finset.mem_union] at hs
  rcases hs with (harc | hchord) | hconn
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp harc
    exact Or.inl ⟨t, ht, rfl⟩
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hchord
    exact Or.inr (Or.inl ⟨t, ht, rfl⟩)
  · rcases mem_auxiliaryCycleConnectorTarget_cases (B.firstGapLeft j)
      (B.firstGapRight j) (B.firstGapFinishSide j - B.firstGapStartSide j)
      hconn with h | ⟨r, hr, rfl⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨r, hr, rfl⟩))

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
