import GroupApproximation.GGT.DGOProposition414GapPartnerSlots
import GroupApproximation.GGT.DGOProposition414GapConnectorComponents

/-!
# Adjacent connector target slots of broken sources

The greedy entry of a broken component has one gap immediately before it and
one immediately after it.  The first contains the chosen start connector on
its right; the second contains the chosen end connector, reversed on its
left.  Empty compressed connectors give absent slots.  These are the two
outer factors in the distributed placement for Dahmani--Guirardel--Osin
Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace HalfGap

/-- The entry child is the gap immediately before its source. -/
theorem nextEntry_entryChild
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L)
    (e : Fin A.sources.length) :
    nextEntry A (HalfEntry.entryChild A e) = some e := by
  simp [nextEntry, HalfEntry.entryChild]

/-- The exit child is the gap immediately after its source. -/
theorem previousEntry_exitChild
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L)
    (e : Fin A.sources.length) :
    previousEntry A (HalfEntry.exitChild A e) = some e := by
  simp [previousEntry, HalfEntry.exitChild]

end HalfGap

namespace BalancedSplitData

/-- Optional right-connector slot immediately before a broken first-half
source. -/
noncomputable def firstBrokenStartSlot
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
  let Q := (B.gapIntervalsOfConfigurations C).toPathInput
  let e := B.firstSourceEntry s hs
  let j := HalfEntry.entryChild B.brokenAssignment.index.first e
  if h : 0 < (B.firstGapRight j).length then
    exact some (Q.firstEntryStartConnectorSlot e 0 h (P.label s) (by
      change B.firstGapLocalLabel j
        ((B.firstGapLeft j).length +
          (B.firstGapFinishSide j - B.firstGapStartSide j) + 0) = P.label s
      have hlabel := B.firstGapLocalLabel_rightConnector j e
        (HalfGap.nextEntry_entryChild B.brokenAssignment.index.first e) 0 h
      simpa [e, j, B.firstSourceEntry_source s hs] using hlabel))
  else exact none

/-- Optional reversed left-connector slot immediately after a broken
first-half source. -/
noncomputable def firstBrokenEndSlot
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
  let Q := (B.gapIntervalsOfConfigurations C).toPathInput
  let e := B.firstSourceEntry s hs
  let j := HalfEntry.exitChild B.brokenAssignment.index.first e
  if h : 0 < (B.firstGapLeft j).length then
    exact some (Q.firstEntryEndConnectorSlot e 0 h (P.label s) (by
      change B.firstGapLocalLabel j 0 = P.label s
      have hlabel := B.firstGapLocalLabel_leftConnector j e
        (HalfGap.previousEntry_exitChild B.brokenAssignment.index.first e) 0 h
      simpa [e, j, B.firstSourceEntry_source s hs] using hlabel))
  else exact none

/-- Optional right-connector slot immediately before a broken wrapped-half
source. -/
noncomputable def secondBrokenStartSlot
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
  let Q := (B.gapIntervalsOfConfigurations C).toPathInput
  let e := B.secondSourceEntry s hs
  let j := HalfEntry.entryChild B.brokenAssignment.index.second e
  if h : 0 < (B.secondGapRight j).length then
    exact some (Q.secondEntryStartConnectorSlot e 0 h (P.label s) (by
      change B.secondGapLocalLabel j
        ((B.secondGapLeft j).length +
          (B.secondGapFinishSide j - B.secondGapStartSide j) + 0) = P.label s
      have hlabel := B.secondGapLocalLabel_rightConnector j e
        (HalfGap.nextEntry_entryChild B.brokenAssignment.index.second e) 0 h
      simpa [e, j, B.secondSourceEntry_source s hs] using hlabel))
  else exact none

/-- Optional reversed left-connector slot immediately after a broken
wrapped-half source. -/
noncomputable def secondBrokenEndSlot
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
  let Q := (B.gapIntervalsOfConfigurations C).toPathInput
  let e := B.secondSourceEntry s hs
  let j := HalfEntry.exitChild B.brokenAssignment.index.second e
  if h : 0 < (B.secondGapLeft j).length then
    exact some (Q.secondEntryEndConnectorSlot e 0 h (P.label s) (by
      change B.secondGapLocalLabel j 0 = P.label s
      have hlabel := B.secondGapLocalLabel_leftConnector j e
        (HalfGap.previousEntry_exitChild B.brokenAssignment.index.second e) 0 h
      simpa [e, j, B.secondSourceEntry_source s hs] using hlabel))
  else exact none

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
