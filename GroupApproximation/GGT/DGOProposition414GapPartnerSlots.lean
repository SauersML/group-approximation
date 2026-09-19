import GroupApproximation.GGT.DGOProposition414GapChordComponents
import GroupApproximation.GGT.DGOProposition414GapIntervalProducer
import GroupApproximation.GGT.DGOProposition414IntervalTargetSlots

/-!
# Opposite-half chord target slots

Each broken component has a selected chord edge, and the cross-half occurrence
construction assigns that edge to an actual child of the opposite half.  This
module packages the assigned local chord coordinate as the tagged middle
target slot used in the factor placement for Dahmani--Guirardel--Osin
Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- The selected chord edge of a broken first-half source, placed in its
canonical wrapped-half child. -/
noncomputable def firstBrokenPartnerSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    TwoHalfTargetSlot
      (B.gapIntervalsOfConfigurations C).toPathInput.family (P.label s) := by
  let Q := (B.gapIntervalsOfConfigurations C).toPathInput
  let j := B.firstPartnerSecondGapOwner s
  let q := B.secondGapChordTargetIndex j
    (B.brokenAssignment.first.partner s)
  apply Q.secondLocalTargetSlot j q (P.label s)
  · change q ∈ B.secondGapLocalTarget j
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    refine ⟨s, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hs, rfl⟩
  · change B.secondGapLocalLabel j q = P.label s
    apply B.secondGapLocalLabel_chord j s
    exact Finset.mem_filter.mpr ⟨hs, rfl⟩

/-- The selected chord edge of a broken wrapped-half source, placed in its
canonical first-half child. -/
noncomputable def secondBrokenPartnerSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    TwoHalfTargetSlot
      (B.gapIntervalsOfConfigurations C).toPathInput.family (P.label s) := by
  let Q := (B.gapIntervalsOfConfigurations C).toPathInput
  let j := B.secondPartnerFirstGapOwner s
  let q := B.firstGapChordTargetIndex j
    (B.brokenAssignment.second.partner s)
  apply Q.firstLocalTargetSlot j q (P.label s)
  · change q ∈ B.firstGapLocalTarget j
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    refine ⟨s, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hs, rfl⟩
  · change B.firstGapLocalLabel j q = P.label s
    apply B.firstGapLocalLabel_chord j s
    exact Finset.mem_filter.mpr ⟨hs, rfl⟩

@[simp]
theorem firstBrokenPartnerSlot_child
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    (B.firstBrokenPartnerSlot C hs).child =
      Sum.inr (B.firstPartnerSecondGapOwner s) := rfl

@[simp]
theorem firstBrokenPartnerSlot_targetIndex
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    (B.firstBrokenPartnerSlot C hs).targetIndex =
      B.secondGapChordTargetIndex (B.firstPartnerSecondGapOwner s)
        (B.brokenAssignment.first.partner s) := rfl

@[simp]
theorem secondBrokenPartnerSlot_child
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    (B.secondBrokenPartnerSlot C hs).child =
      Sum.inl (B.secondPartnerFirstGapOwner s) := rfl

@[simp]
theorem secondBrokenPartnerSlot_targetIndex
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    (B.secondBrokenPartnerSlot C hs).targetIndex =
      B.firstGapChordTargetIndex (B.secondPartnerFirstGapOwner s)
        (B.brokenAssignment.second.partner s) := rfl

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
