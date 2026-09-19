import GroupApproximation.GGT.DGOProposition414GapSurvivorOwner
import GroupApproximation.GGT.DGOProposition414GapIntervalProducer
import GroupApproximation.GGT.DGOProposition414IntervalTargetSlots

/-!
# Child target slots of surviving balanced components

Every target which survives a balanced half cut is an inherited target in its
canonical gap child.  This module turns the gap-owner theorem into the actual
tagged target slots used by the distributed factor placement in
Dahmani--Guirardel--Osin Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- Local side coordinate of a surviving first-half target in its gap. -/
noncomputable def firstSurvivorLocalIndex
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.componentPlacement.firstTarget)
    (hsurvives : B.componentPlacement.firstSurvives s) : ℕ :=
  (B.firstGapLeft (B.firstSurvivorGapOwner hs hsurvives)).length +
    (B.firstTargetSide s -
      B.firstGapStartSide (B.firstSurvivorGapOwner hs hsurvives))

/-- Local side coordinate of a surviving wrapped-half target in its gap. -/
noncomputable def secondSurvivorLocalIndex
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.componentPlacement.secondTarget)
    (hsurvives : B.componentPlacement.secondSurvives s) : ℕ :=
  (B.secondGapLeft (B.secondSurvivorGapOwner hs hsurvives)).length +
    (B.secondTargetSide s -
      B.secondGapStartSide (B.secondSurvivorGapOwner hs hsurvives))

/-- A surviving first-half target gives one actual target slot. -/
noncomputable def firstSurvivorSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ B.componentPlacement.firstTarget)
    (hsurvives : B.componentPlacement.firstSurvives s) :
    TwoHalfTargetSlot
      (B.gapIntervalsOfConfigurations C).toPathInput.family (P.label s) := by
  let Q := (B.gapIntervalsOfConfigurations C).toPathInput
  let j := B.firstSurvivorGapOwner hs hsurvives
  let q := B.firstSurvivorLocalIndex hs hsurvives
  apply Q.firstLocalTargetSlot j q (P.label s)
  · change q ∈ B.firstGapLocalTarget j
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_image.mpr
    exact ⟨s, B.firstSurvivorGapOwner_mem hs hsurvives, rfl⟩
  · change B.firstGapLocalLabel j q = P.label s
    exact B.firstGapLocalLabel_arc j s
      (B.firstSurvivorGapOwner_mem hs hsurvives)

/-- A surviving wrapped-half target gives one actual target slot. -/
noncomputable def secondSurvivorSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ B.componentPlacement.secondTarget)
    (hsurvives : B.componentPlacement.secondSurvives s) :
    TwoHalfTargetSlot
      (B.gapIntervalsOfConfigurations C).toPathInput.family (P.label s) := by
  let Q := (B.gapIntervalsOfConfigurations C).toPathInput
  let j := B.secondSurvivorGapOwner hs hsurvives
  let q := B.secondSurvivorLocalIndex hs hsurvives
  apply Q.secondLocalTargetSlot j q (P.label s)
  · change q ∈ B.secondGapLocalTarget j
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_image.mpr
    exact ⟨s, B.secondSurvivorGapOwner_mem hs hsurvives, rfl⟩
  · change B.secondGapLocalLabel j q = P.label s
    exact B.secondGapLocalLabel_arc j s
      (B.secondSurvivorGapOwner_mem hs hsurvives)

@[simp]
theorem firstSurvivorSlot_child
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ B.componentPlacement.firstTarget)
    (hsurvives : B.componentPlacement.firstSurvives s) :
    (B.firstSurvivorSlot C hs hsurvives).child =
      Sum.inl (B.firstSurvivorGapOwner hs hsurvives) := rfl

@[simp]
theorem firstSurvivorSlot_targetIndex
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ B.componentPlacement.firstTarget)
    (hsurvives : B.componentPlacement.firstSurvives s) :
    (B.firstSurvivorSlot C hs hsurvives).targetIndex =
      B.firstSurvivorLocalIndex hs hsurvives := rfl

@[simp]
theorem secondSurvivorSlot_child
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ B.componentPlacement.secondTarget)
    (hsurvives : B.componentPlacement.secondSurvives s) :
    (B.secondSurvivorSlot C hs hsurvives).child =
      Sum.inr (B.secondSurvivorGapOwner hs hsurvives) := rfl

@[simp]
theorem secondSurvivorSlot_targetIndex
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ B.componentPlacement.secondTarget)
    (hsurvives : B.componentPlacement.secondSurvives s) :
    (B.secondSurvivorSlot C hs hsurvives).targetIndex =
      B.secondSurvivorLocalIndex hs hsurvives := rfl

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
