import GroupApproximation.GGT.DGOProposition414GapSurvivorSlotSpans

/-!
# Signed factors of broken balanced components

The connector on either side of a broken component may already include its
selected chord edge.  The remaining middle factor is present exactly when
both adjacent gap orientations agree, and it is read with the sign required
by the source half.  These are the type-(2)--(4) factor identities in
Dahmani--Guirardel--Osin Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace ComponentConnectorPair

/-- The compressed entry-through-partner connector is the entry connector
followed by the selected partner span. -/
theorem startThroughPartner_value_factorization
    {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {word : List (RelLetter G Λ)} {source partner : ℕ}
    (C : ComponentConnectorPair D lam v word source partner) :
    RelLetter.listVal C.startThroughPartner =
      RelLetter.listVal C.startConnector *
        ((vertex v word partner)⁻¹ * vertex v word C.partnerEnd) := by
  rw [C.startThroughPartner_value, C.start_value]
  group

/-- The compressed exit-through-partner connector is the exit connector
followed by the inverse selected partner span. -/
theorem endThroughPartner_value_factorization
    {D : RelGenSet G Λ} {lam : Λ} {v : G}
    {word : List (RelLetter G Λ)} {source partner : ℕ}
    (C : ComponentConnectorPair D lam v word source partner) :
    RelLetter.listVal C.endThroughPartner =
      RelLetter.listVal C.endConnector *
        ((vertex v word partner)⁻¹ * vertex v word C.partnerEnd)⁻¹ := by
  rw [C.endThroughPartner_value, C.end_value]
  group

end ComponentConnectorPair

namespace BalancedSplitData

/-- Orientation of the gap immediately before a broken first-half source. -/
noncomputable def firstBrokenEntryForward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) : Prop :=
  B.firstGapRunsForward
    (HalfEntry.entryChild B.brokenAssignment.index.first
      (B.firstSourceEntry s hs))

/-- Orientation of the gap immediately after a broken first-half source. -/
noncomputable def firstBrokenExitForward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) : Prop :=
  B.firstGapRunsForward
    (HalfEntry.exitChild B.brokenAssignment.index.first
      (B.firstSourceEntry s hs))

/-- Orientation of the gap immediately before a broken wrapped-half source. -/
noncomputable def secondBrokenEntryForward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) : Prop :=
  B.secondGapRunsForward
    (HalfEntry.entryChild B.brokenAssignment.index.second
      (B.secondSourceEntry s hs))

/-- Orientation of the gap immediately after a broken wrapped-half source. -/
noncomputable def secondBrokenExitForward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) : Prop :=
  B.secondGapRunsForward
    (HalfEntry.exitChild B.brokenAssignment.index.second
      (B.secondSourceEntry s hs))

/-- A first-half broken source needs a separate middle chord factor exactly
when its adjacent gap orientations agree. -/
noncomputable def firstBrokenMiddleSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    Option (TwoHalfTargetSlot
      (B.gapIntervalsOfConfigurations C).toPathInput.family (P.label s)) := by
  classical
  exact if B.firstBrokenEntryForward hs ↔ B.firstBrokenExitForward hs then
    some (B.firstBrokenPartnerSlot C hs) else none

/-- Wrapped-half counterpart of `firstBrokenMiddleSlot`. -/
noncomputable def secondBrokenMiddleSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    Option (TwoHalfTargetSlot
      (B.gapIntervalsOfConfigurations C).toPathInput.family (P.label s)) := by
  classical
  exact if B.secondBrokenEntryForward hs ↔ B.secondBrokenExitForward hs then
    some (B.secondBrokenPartnerSlot C hs) else none

/-- The middle target is inverted exactly when its child orientation agrees
with the adjacent source-gap orientation. -/
noncomputable def firstBrokenMiddleInverted
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) : Prop :=
  B.firstBrokenEntryForward hs ↔
    B.secondGapChordStart (B.firstPartnerSecondGapOwner s) ≤
      B.secondGapChordFinish (B.firstPartnerSecondGapOwner s)

/-- Wrapped-half counterpart of `firstBrokenMiddleInverted`. -/
noncomputable def secondBrokenMiddleInverted
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) : Prop :=
  B.secondBrokenEntryForward hs ↔
    B.firstGapChordStart (B.secondPartnerFirstGapOwner s) ≤
      B.firstGapChordFinish (B.secondPartnerFirstGapOwner s)

/-- The original first-half source span is the source span stored in its
connector pair. -/
theorem firstBroken_sourceSpan_eq
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    P.span s =
      (vertex B.firstBase B.firstWord (B.componentPlacement.firstPos s))⁻¹ *
        vertex B.firstBase B.firstWord
          (B.firstBrokenConnectors s hs).sourceEnd := by
  have hsTarget := (mem_brokenSet_iff.mp hs).1
  let C := B.firstBrokenConnectors s hs
  have hposLt := B.componentPlacement.first_pos_lt s hsTarget
  have hsourceEnd := C.source_end_eq
  have hletter :
      B.firstWord[B.componentPlacement.firstPos s]'hposLt =
        B.firstArc[B.firstTargetPos s]'
          (B.firstTargetPos_lt_firstArc_length hsTarget) := by
    change (B.firstArc ++ revWord B.chord)[B.firstTargetPos s]'_ = _
    rw [List.getElem_append_left
      (B.firstTargetPos_lt_firstArc_length hsTarget)]
  rw [hsourceEnd]
  calc
    P.span s =
        (B.firstArc[B.firstTargetPos s]'
          (B.firstTargetPos_lt_firstArc_length hsTarget)).val :=
      (B.firstTarget_arcLetter_val_eq_span hsTarget).symm
    _ = (B.firstWord[B.componentPlacement.firstPos s]'hposLt).val := by
      rw [hletter]
    _ = (vertex B.firstBase B.firstWord
          (B.componentPlacement.firstPos s))⁻¹ *
        vertex B.firstBase B.firstWord
          (B.componentPlacement.firstPos s + 1) := by
      rw [vertex_succ B.firstWord B.firstBase
        (B.componentPlacement.firstPos s) hposLt]
      group

/-- The original wrapped-half source span is the source span stored in its
connector pair. -/
theorem secondBroken_sourceSpan_eq
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    P.span s =
      (vertex B.secondBase B.secondWord (B.componentPlacement.secondPos s))⁻¹ *
        vertex B.secondBase B.secondWord
          (B.secondBrokenConnectors s hs).sourceEnd := by
  have hsTarget := (mem_brokenSet_iff.mp hs).1
  let C := B.secondBrokenConnectors s hs
  have hposLt := B.componentPlacement.second_pos_lt s hsTarget
  have hsourceEnd := C.source_end_eq
  have hword : B.secondWord = B.secondArc ++ B.chord := by
    have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
      simp [refinedCut, splitPairCut_left B.side_order]
    have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
      simp [refinedCut, splitPairCut_right]
    unfold secondWord secondArc
    simp only [secondHalf]
    rw [hleft, hright]
  have hletter :
      B.secondWord[B.componentPlacement.secondPos s]'hposLt =
        B.secondArc[B.secondTargetPos s]'
          (B.secondTargetPos_lt_secondArc_length hsTarget) := by
    rw [hword]
    change (B.secondArc ++ B.chord)[B.secondTargetPos s]'_ = _
    rw [List.getElem_append_left
      (B.secondTargetPos_lt_secondArc_length hsTarget)]
  rw [hsourceEnd]
  calc
    P.span s =
        (B.secondArc[B.secondTargetPos s]'
          (B.secondTargetPos_lt_secondArc_length hsTarget)).val :=
      (B.secondTarget_arcLetter_val_eq_span hsTarget).symm
    _ = (B.secondWord[B.componentPlacement.secondPos s]'hposLt).val := by
      rw [hletter]
    _ = (vertex B.secondBase B.secondWord
          (B.componentPlacement.secondPos s))⁻¹ *
        vertex B.secondBase B.secondWord
          (B.componentPlacement.secondPos s + 1) := by
      rw [vertex_succ B.secondWord B.secondBase
        (B.componentPlacement.secondPos s) hposLt]
      group

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
