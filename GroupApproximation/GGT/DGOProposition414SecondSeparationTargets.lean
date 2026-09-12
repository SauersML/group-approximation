import GroupApproximation.GGT.DGOProposition414FirstSeparationTargets

/-! # The four target classes of a wrapped auxiliary cycle -/

namespace GroupApproximation.GGT.DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- Every distinguished side of a second-half gap child is an inherited arc
target, a charged partner edge, a left connector letter or a right connector
letter. -/
theorem secondGapTarget_cases
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    {s : ℕ} (hs : s ∈ B.secondGapTarget j) :
    (∃ t ∈ B.secondGapArcSources j,
        s = (B.secondGapLeft j).length +
          (B.secondTargetSide t - B.secondGapStartSide j)) ∨
      (∃ t ∈ B.secondGapChordSources j,
        s = B.secondGapChordTargetIndex j
          (B.brokenAssignment.first.partner t)) ∨
      s < (B.secondGapLeft j).length ∨
      (∃ r : ℕ, r < (B.secondGapRight j).length ∧
        s = (B.secondGapLeft j).length +
          (B.secondGapFinishSide j - B.secondGapStartSide j) + r) := by
  classical
  simp only [secondGapTarget, secondGapLocalTarget, Finset.mem_union] at hs
  rcases hs with (harc | hchord) | hconn
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp harc
    exact Or.inl ⟨t, ht, rfl⟩
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hchord
    exact Or.inr (Or.inl ⟨t, ht, rfl⟩)
  · rcases mem_auxiliaryCycleConnectorTarget_cases (B.secondGapLeft j)
      (B.secondGapRight j) (B.secondGapFinishSide j - B.secondGapStartSide j)
      hconn with h | ⟨r, hr, rfl⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨r, hr, rfl⟩))

end BalancedSplitData

end GroupApproximation.GGT.DGOProposition414

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapTarget_cases
