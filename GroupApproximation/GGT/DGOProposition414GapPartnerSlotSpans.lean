import GroupApproximation.GGT.DGOProposition414GapConnectorSlotSpans

/-!
# Spans of opposite-half partner slots

The middle slot of a broken source is its selected global chord edge in the
opposite-half child.  Its span is the forward chord-letter value or its inverse
according to that child's oriented chord segment.  This is the type-(4) factor
calculation in Dahmani--Guirardel--Osin Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- Span of the opposite wrapped-half partner slot of a broken first-half
source. -/
theorem firstBrokenPartnerSlot_span
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    optionalTargetSlotSpan (some (B.firstBrokenPartnerSlot C hs)) =
      if B.secondGapChordStart (B.firstPartnerSecondGapOwner s) ≤
          B.secondGapChordFinish (B.firstPartnerSecondGapOwner s) then
        (B.chord[B.brokenAssignment.first.partner s]'
          (B.brokenAssignment.first.partner_lt s hs)).val
      else
        (B.chord[B.brokenAssignment.first.partner s]'
          (B.brokenAssignment.first.partner_lt s hs)).val⁻¹ := by
  let Q := (B.gapIntervalsOfConfigurations C).toPathInput
  let j := B.firstPartnerSecondGapOwner s
  let y := B.brokenAssignment.first.partner s
  let r := orientedEdgeIndex (B.secondGapChordStart j)
    (B.secondGapChordFinish j) y
  have hedge := B.firstPartnerSecondGapOwner_edge s hs
  change (Q.second j).certificate.sideSpan
      ((Q.second j).left.length + (Q.second j).arcSides +
        (Q.second j).right.length + r) =
    if B.secondGapChordStart j ≤ B.secondGapChordFinish j then
      (B.chord[y]'(B.brokenAssignment.first.partner_lt s hs)).val
    else (B.chord[y]'(B.brokenAssignment.first.partner_lt s hs)).val⁻¹
  calc
    _ = ((Q.second j).chord[r]'(by
        change r < (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)).length
        exact orientedEdgeIndex_lt B.chord
          (B.secondGapChordStart_le j) (B.secondGapChordFinish_le j)
          hedge)).val :=
      (Q.second j).chord_sideSpan_eq_letter r (by
        change r < (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)).length
        exact orientedEdgeIndex_lt B.chord
          (B.secondGapChordStart_le j) (B.secondGapChordFinish_le j)
          hedge)
    _ = _ := by
      change ((orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j))[r]'_).val = _
      exact orientedEdgeIndex_val B.chord
        (B.secondGapChordStart_le j) (B.secondGapChordFinish_le j)
        (B.brokenAssignment.first.partner_lt s hs) hedge

/-- Span of the opposite first-half partner slot of a broken wrapped-half
source. -/
theorem secondBrokenPartnerSlot_span
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    optionalTargetSlotSpan (some (B.secondBrokenPartnerSlot C hs)) =
      if B.firstGapChordStart (B.secondPartnerFirstGapOwner s) ≤
          B.firstGapChordFinish (B.secondPartnerFirstGapOwner s) then
        (B.chord[B.brokenAssignment.second.partner s]'
          (B.brokenAssignment.second.partner_lt s hs)).val
      else
        (B.chord[B.brokenAssignment.second.partner s]'
          (B.brokenAssignment.second.partner_lt s hs)).val⁻¹ := by
  let Q := (B.gapIntervalsOfConfigurations C).toPathInput
  let j := B.secondPartnerFirstGapOwner s
  let y := B.brokenAssignment.second.partner s
  let r := orientedEdgeIndex (B.firstGapChordStart j)
    (B.firstGapChordFinish j) y
  have hedge := B.secondPartnerFirstGapOwner_edge s hs
  change (Q.first j).certificate.sideSpan
      ((Q.first j).left.length + (Q.first j).arcSides +
        (Q.first j).right.length + r) =
    if B.firstGapChordStart j ≤ B.firstGapChordFinish j then
      (B.chord[y]'(B.brokenAssignment.second.partner_lt s hs)).val
    else (B.chord[y]'(B.brokenAssignment.second.partner_lt s hs)).val⁻¹
  calc
    _ = ((Q.first j).chord[r]'(by
        change r < (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)).length
        exact orientedEdgeIndex_lt B.chord
          (B.firstGapChordStart_le j) (B.firstGapChordFinish_le j)
          hedge)).val :=
      (Q.first j).chord_sideSpan_eq_letter r (by
        change r < (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)).length
        exact orientedEdgeIndex_lt B.chord
          (B.firstGapChordStart_le j) (B.firstGapChordFinish_le j)
          hedge)
    _ = _ := by
      change ((orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j))[r]'_).val = _
      exact orientedEdgeIndex_val B.chord
        (B.firstGapChordStart_le j) (B.firstGapChordFinish_le j)
        (B.brokenAssignment.second.partner_lt s hs) hedge

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
