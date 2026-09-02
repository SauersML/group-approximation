import GroupApproximation.GGT.DGOProposition414TargetSlotSpans

/-!
# Spans of the optional broken-source connector slots

The right connector before a broken source is read forward, while the left
connector after it is read backwards.  Empty compressed connectors contribute
the identity.  This module computes all four optional spans needed by the
distributed factorization in Dahmani--Guirardel--Osin Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- The first-half start slot is exactly the value of the right connector in
the entry child. -/
theorem firstBrokenStartSlot_span
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    optionalTargetSlotSpan (B.firstBrokenStartSlot C hs) =
      RelLetter.listVal (B.firstGapRight
        (B.firstBrokenOwner s hs)) := by
  let Q := (B.gapIntervalsOfConfigurations C).toPathInput
  let e := B.firstSourceEntry s hs
  let j := HalfEntry.entryChild B.brokenAssignment.index.first e
  change optionalTargetSlotSpan (B.firstBrokenStartSlot C hs) =
    RelLetter.listVal (B.firstGapRight j)
  unfold firstBrokenStartSlot
  split
  next h =>
    change (Q.first j).certificate.sideSpan
      ((Q.first j).left.length + (Q.first j).arcSides) =
        RelLetter.listVal (B.firstGapRight j)
    change (Q.first j).certificate.sideSpan
      ((Q.first j).left.length + (Q.first j).arcSides) =
        RelLetter.listVal (Q.first j).right
    exact (Q.first j).rightConnector_sideSpan h
      (B.firstGapRight_length_le_one j)
  next h =>
    have hzero : (B.firstGapRight j).length = 0 := by omega
    have hempty : B.firstGapRight j = [] := List.length_eq_zero_iff.mp hzero
    simp [optionalTargetSlotSpan, hempty]

/-- The first-half end slot is the inverse value of the left connector in the
exit child. -/
theorem firstBrokenEndSlot_span
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    optionalTargetSlotSpan (B.firstBrokenEndSlot C hs) =
      (RelLetter.listVal (B.firstGapLeft
        (HalfEntry.exitChild B.brokenAssignment.index.first
          (B.firstSourceEntry s hs))))⁻¹ := by
  let Q := (B.gapIntervalsOfConfigurations C).toPathInput
  let e := B.firstSourceEntry s hs
  let j := HalfEntry.exitChild B.brokenAssignment.index.first e
  change optionalTargetSlotSpan (B.firstBrokenEndSlot C hs) =
    (RelLetter.listVal (B.firstGapLeft j))⁻¹
  unfold firstBrokenEndSlot
  split
  next h =>
    change (Q.first j).certificate.sideSpan 0 =
      (RelLetter.listVal (B.firstGapLeft j))⁻¹
    change (Q.first j).certificate.sideSpan 0 =
      (RelLetter.listVal (Q.first j).left)⁻¹
    exact (Q.first j).leftConnector_sideSpan h
      (B.firstGapLeft_length_le_one j)
  next h =>
    have hzero : (B.firstGapLeft j).length = 0 := by omega
    have hempty : B.firstGapLeft j = [] := List.length_eq_zero_iff.mp hzero
    simp [optionalTargetSlotSpan, hempty]

/-- Wrapped-half counterpart for the start slot. -/
theorem secondBrokenStartSlot_span
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    optionalTargetSlotSpan (B.secondBrokenStartSlot C hs) =
      RelLetter.listVal (B.secondGapRight
        (B.secondBrokenOwner s hs)) := by
  let Q := (B.gapIntervalsOfConfigurations C).toPathInput
  let e := B.secondSourceEntry s hs
  let j := HalfEntry.entryChild B.brokenAssignment.index.second e
  change optionalTargetSlotSpan (B.secondBrokenStartSlot C hs) =
    RelLetter.listVal (B.secondGapRight j)
  unfold secondBrokenStartSlot
  split
  next h =>
    change (Q.second j).certificate.sideSpan
      ((Q.second j).left.length + (Q.second j).arcSides) =
        RelLetter.listVal (B.secondGapRight j)
    change (Q.second j).certificate.sideSpan
      ((Q.second j).left.length + (Q.second j).arcSides) =
        RelLetter.listVal (Q.second j).right
    exact (Q.second j).rightConnector_sideSpan h
      (B.secondGapRight_length_le_one j)
  next h =>
    have hzero : (B.secondGapRight j).length = 0 := by omega
    have hempty : B.secondGapRight j = [] := List.length_eq_zero_iff.mp hzero
    simp [optionalTargetSlotSpan, hempty]

/-- Wrapped-half counterpart for the reversed end slot. -/
theorem secondBrokenEndSlot_span
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    optionalTargetSlotSpan (B.secondBrokenEndSlot C hs) =
      (RelLetter.listVal (B.secondGapLeft
        (HalfEntry.exitChild B.brokenAssignment.index.second
          (B.secondSourceEntry s hs))))⁻¹ := by
  let Q := (B.gapIntervalsOfConfigurations C).toPathInput
  let e := B.secondSourceEntry s hs
  let j := HalfEntry.exitChild B.brokenAssignment.index.second e
  change optionalTargetSlotSpan (B.secondBrokenEndSlot C hs) =
    (RelLetter.listVal (B.secondGapLeft j))⁻¹
  unfold secondBrokenEndSlot
  split
  next h =>
    change (Q.second j).certificate.sideSpan 0 =
      (RelLetter.listVal (B.secondGapLeft j))⁻¹
    change (Q.second j).certificate.sideSpan 0 =
      (RelLetter.listVal (Q.second j).left)⁻¹
    exact (Q.second j).leftConnector_sideSpan h
      (B.secondGapLeft_length_le_one j)
  next h =>
    have hzero : (B.secondGapLeft j).length = 0 := by omega
    have hempty : B.secondGapLeft j = [] := List.length_eq_zero_iff.mp hzero
    simp [optionalTargetSlotSpan, hempty]

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
