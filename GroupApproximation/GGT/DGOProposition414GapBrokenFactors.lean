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

/-- Connector pair attached to the actual greedy entry chosen for a broken
first-half source. -/
noncomputable def firstBrokenEntryConnectors
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :=
  B.firstBrokenConnectors
    (HalfEntry.entrySource B.brokenAssignment.index.first
      (B.firstSourceEntry s hs))
    (HalfEntry.entrySource_mem B.brokenAssignment.index.first
      (B.firstSourceEntry s hs))

/-- Connector pair attached to the actual greedy entry chosen for a broken
wrapped-half source. -/
noncomputable def secondBrokenEntryConnectors
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :=
  B.secondBrokenConnectors
    (HalfEntry.entrySource B.brokenAssignment.index.second
      (B.secondSourceEntry s hs))
    (HalfEntry.entrySource_mem B.brokenAssignment.index.second
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
  change s ∈ B.firstTarget at hsTarget
  let C := B.firstBrokenConnectors s hs
  have hposLt : B.componentPlacement.firstPos s < B.firstWord.length := by
    obtain ⟨t, ht⟩ := B.componentPlacement.first_start s hsTarget
    exact ht.1.trans_le ht.2.1
  change B.firstTargetPos s < B.firstWord.length at hposLt
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
  change s ∈ B.secondTarget at hsTarget
  let C := B.secondBrokenConnectors s hs
  have hposLt : B.componentPlacement.secondPos s < B.secondWord.length := by
    obtain ⟨t, ht⟩ := B.componentPlacement.second_start s hsTarget
    exact ht.1.trans_le ht.2.1
  change B.secondTargetPos s < B.secondWord.length at hposLt
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
    let p := B.secondTargetPos s
    have hpArc : p < B.secondArc.length :=
      B.secondTargetPos_lt_secondArc_length hsTarget
    have hpAppend : p < (B.secondArc ++ B.chord).length := by
      rw [List.length_append]
      omega
    have hopt := congrArg (fun w : List (RelLetter G Λ) => w[p]?) hword
    rw [List.getElem?_eq_getElem hposLt,
      List.getElem?_eq_getElem hpAppend] at hopt
    have hget : B.secondWord[p]'hposLt =
        (B.secondArc ++ B.chord)[p]'hpAppend := Option.some.inj hopt
    calc
      _ = (B.secondArc ++ B.chord)[p]'hpAppend := hget
      _ = B.secondArc[p]'hpArc := by
        rw [List.getElem_append_left hpArc]
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

/-! ## Values of the three actual broken-source slots -/

/-- The first-half entry slot is the plain entry connector in the forward
case and the entry-through-partner connector in the reverse case. -/
theorem firstBrokenStartSlot_span_cases
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    (B.firstBrokenEntryForward hs →
      optionalTargetSlotSpan (B.firstBrokenStartSlot C hs) =
        RelLetter.listVal (B.firstBrokenEntryConnectors hs).startConnector) ∧
    (¬ B.firstBrokenEntryForward hs →
      optionalTargetSlotSpan (B.firstBrokenStartSlot C hs) =
        RelLetter.listVal
          (B.firstBrokenEntryConnectors hs).startThroughPartner) := by
  constructor <;> intro hf
  · rw [B.firstBrokenStartSlot_span C hs]
    have hf' : B.firstGapRunsForward
        (HalfEntry.entryChild B.brokenAssignment.index.first
          (B.firstSourceEntry s hs)) := hf
    unfold firstBrokenOwner firstGapRight
    rw [HalfGap.nextEntry_entryChild]
    simp only [hf', ↓reduceIte]
    rfl
  · rw [B.firstBrokenStartSlot_span C hs]
    have hf' : ¬ B.firstGapRunsForward
        (HalfEntry.entryChild B.brokenAssignment.index.first
          (B.firstSourceEntry s hs)) := hf
    unfold firstBrokenOwner firstGapRight
    rw [HalfGap.nextEntry_entryChild]
    simp only [hf', ↓reduceIte]
    rfl

/-- The first-half exit slot is the inverse plain exit connector in the
forward case and the inverse exit-through-partner connector in reverse. -/
theorem firstBrokenEndSlot_span_cases
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    (B.firstBrokenExitForward hs →
      optionalTargetSlotSpan (B.firstBrokenEndSlot C hs) =
        (RelLetter.listVal
          (B.firstBrokenEntryConnectors hs).endConnector)⁻¹) ∧
    (¬ B.firstBrokenExitForward hs →
      optionalTargetSlotSpan (B.firstBrokenEndSlot C hs) =
        (RelLetter.listVal
          (B.firstBrokenEntryConnectors hs).endThroughPartner)⁻¹) := by
  constructor <;> intro hf
  · rw [B.firstBrokenEndSlot_span C hs]
    have hf' : B.firstGapRunsForward
        (HalfEntry.exitChild B.brokenAssignment.index.first
          (B.firstSourceEntry s hs)) := hf
    unfold firstGapLeft
    rw [HalfGap.previousEntry_exitChild]
    simp only [hf', ↓reduceIte]
    rfl
  · rw [B.firstBrokenEndSlot_span C hs]
    have hf' : ¬ B.firstGapRunsForward
        (HalfEntry.exitChild B.brokenAssignment.index.first
          (B.firstSourceEntry s hs)) := hf
    unfold firstGapLeft
    rw [HalfGap.previousEntry_exitChild]
    simp only [hf', ↓reduceIte]
    rfl

/-- The wrapped entry convention is opposite: forward gaps use the
entry-through-partner connector. -/
theorem secondBrokenStartSlot_span_cases
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    (B.secondBrokenEntryForward hs →
      optionalTargetSlotSpan (B.secondBrokenStartSlot C hs) =
        RelLetter.listVal
          (B.secondBrokenEntryConnectors hs).startThroughPartner) ∧
    (¬ B.secondBrokenEntryForward hs →
      optionalTargetSlotSpan (B.secondBrokenStartSlot C hs) =
        RelLetter.listVal
          (B.secondBrokenEntryConnectors hs).startConnector) := by
  constructor <;> intro hf
  · rw [B.secondBrokenStartSlot_span C hs]
    have hf' : B.secondGapRunsForward
        (HalfEntry.entryChild B.brokenAssignment.index.second
          (B.secondSourceEntry s hs)) := hf
    unfold secondBrokenOwner secondGapRight
    rw [HalfGap.nextEntry_entryChild]
    simp only [hf', ↓reduceIte]
    rfl
  · rw [B.secondBrokenStartSlot_span C hs]
    have hf' : ¬ B.secondGapRunsForward
        (HalfEntry.entryChild B.brokenAssignment.index.second
          (B.secondSourceEntry s hs)) := hf
    unfold secondBrokenOwner secondGapRight
    rw [HalfGap.nextEntry_entryChild]
    simp only [hf', ↓reduceIte]
    rfl

/-- Forward wrapped exit gaps use the inverse exit-through-partner
connector; reverse gaps use the inverse plain connector. -/
theorem secondBrokenEndSlot_span_cases
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    (B.secondBrokenExitForward hs →
      optionalTargetSlotSpan (B.secondBrokenEndSlot C hs) =
        (RelLetter.listVal
          (B.secondBrokenEntryConnectors hs).endThroughPartner)⁻¹) ∧
    (¬ B.secondBrokenExitForward hs →
      optionalTargetSlotSpan (B.secondBrokenEndSlot C hs) =
        (RelLetter.listVal
          (B.secondBrokenEntryConnectors hs).endConnector)⁻¹) := by
  constructor <;> intro hf
  · rw [B.secondBrokenEndSlot_span C hs]
    have hf' : B.secondGapRunsForward
        (HalfEntry.exitChild B.brokenAssignment.index.second
          (B.secondSourceEntry s hs)) := hf
    unfold secondGapLeft
    rw [HalfGap.previousEntry_exitChild]
    simp only [hf', ↓reduceIte]
    rfl
  · rw [B.secondBrokenEndSlot_span C hs]
    have hf' : ¬ B.secondGapRunsForward
        (HalfEntry.exitChild B.brokenAssignment.index.second
          (B.secondSourceEntry s hs)) := hf
    unfold secondGapLeft
    rw [HalfGap.previousEntry_exitChild]
    simp only [hf', ↓reduceIte]
    rfl

/-- The selected first-half partner span is the inverse forward global-chord
edge value. -/
theorem firstBroken_partnerSpan_eq_chordInv
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    (vertex B.firstBase B.firstWord
        (B.firstChordPos (B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first
            (B.firstSourceEntry s hs)))))⁻¹ *
      vertex B.firstBase B.firstWord
        (B.firstBrokenConnectors s hs).partnerEnd =
      (B.chord[B.brokenAssignment.first.partner s]'
        (B.brokenAssignment.first.partner_lt s hs)).val⁻¹ := by
  rw [B.firstBrokenConnectors_partnerStart_vertex s hs,
    B.firstBrokenConnectors_partnerEnd_vertex s hs,
    vertex_succ B.chord B.firstBase
      (B.brokenAssignment.first.partner s)
      (B.brokenAssignment.first.partner_lt s hs)]
  group

/-- The selected wrapped-half partner span is the forward global-chord edge
value. -/
theorem secondBroken_partnerSpan_eq_chord
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    (vertex B.secondBase B.secondWord
        (B.secondChordPos (B.brokenAssignment.second.partner s)))⁻¹ *
      vertex B.secondBase B.secondWord
        (B.secondBrokenConnectors s hs).partnerEnd =
      (B.chord[B.brokenAssignment.second.partner s]'
        (B.brokenAssignment.second.partner_lt s hs)).val := by
  rw [B.secondBrokenConnectors_partnerStart_vertex s hs,
    B.secondBrokenConnectors_partnerEnd_vertex s hs,
    vertex_succ B.chord B.firstBase
      (B.brokenAssignment.second.partner s)
      (B.brokenAssignment.second.partner_lt s hs)]
  group

/-! ## Greedy-entry connector spans -/

/-- The connector pair selected through the greedy entry has the original
first-half source span. -/
theorem firstBrokenEntry_sourceSpan_eq
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
          (B.firstBrokenEntryConnectors hs).sourceEnd := by
  let t := HalfEntry.entrySource B.brokenAssignment.index.first
    (B.firstSourceEntry s hs)
  let ht := HalfEntry.entrySource_mem B.brokenAssignment.index.first
    (B.firstSourceEntry s hs)
  let E := B.firstBrokenEntryConnectors hs
  have h := B.firstBroken_sourceSpan_eq ht
  change P.span t =
    (vertex B.firstBase B.firstWord (B.componentPlacement.firstPos t))⁻¹ *
      vertex B.firstBase B.firstWord E.sourceEnd at h
  have hsource : t = s := B.firstSourceEntry_source s hs
  rw [hsource] at h
  exact h

/-- The greedy-entry first-half partner span is the inverse global chord
edge selected for the source. -/
theorem firstBrokenEntry_partnerSpan_eq_chordInv
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    (vertex B.firstBase B.firstWord
        (B.firstChordPos (B.brokenAssignment.first.partner s)))⁻¹ *
      vertex B.firstBase B.firstWord
        (B.firstBrokenEntryConnectors hs).partnerEnd =
      (B.chord[B.brokenAssignment.first.partner s]'
        (B.brokenAssignment.first.partner_lt s hs)).val⁻¹ := by
  let t := HalfEntry.entrySource B.brokenAssignment.index.first
    (B.firstSourceEntry s hs)
  let ht := HalfEntry.entrySource_mem B.brokenAssignment.index.first
    (B.firstSourceEntry s hs)
  let E := B.firstBrokenEntryConnectors hs
  have h := B.firstBroken_partnerSpan_eq_chordInv ht
  change (vertex B.firstBase B.firstWord
      (B.firstChordPos (B.brokenAssignment.first.partner t)))⁻¹ *
    vertex B.firstBase B.firstWord E.partnerEnd =
      (B.chord[B.brokenAssignment.first.partner t]'_).val⁻¹ at h
  have hsource : t = s := B.firstSourceEntry_source s hs
  have hpartner : B.brokenAssignment.first.partner t =
      B.brokenAssignment.first.partner s := congrArg _ hsource
  change (vertex B.firstBase B.firstWord
      (B.firstChordPos (B.brokenAssignment.first.partner t)))⁻¹ *
    vertex B.firstBase B.firstWord E.partnerEnd = _
  calc
    _ = (B.chord[B.brokenAssignment.first.partner t]'_).val⁻¹ := h
    _ = (B.chord[B.brokenAssignment.first.partner s]'_).val⁻¹ := by
      rw [getElem_congr_idx hpartner]

/-- The connector pair selected through the greedy entry has the original
wrapped-half source span. -/
theorem secondBrokenEntry_sourceSpan_eq
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
          (B.secondBrokenEntryConnectors hs).sourceEnd := by
  let t := HalfEntry.entrySource B.brokenAssignment.index.second
    (B.secondSourceEntry s hs)
  let ht := HalfEntry.entrySource_mem B.brokenAssignment.index.second
    (B.secondSourceEntry s hs)
  let E := B.secondBrokenEntryConnectors hs
  have h := B.secondBroken_sourceSpan_eq ht
  change P.span t =
    (vertex B.secondBase B.secondWord (B.componentPlacement.secondPos t))⁻¹ *
      vertex B.secondBase B.secondWord E.sourceEnd at h
  have hsource : t = s := B.secondSourceEntry_source s hs
  rw [hsource] at h
  exact h

/-- The greedy-entry wrapped partner span is the forward global chord edge
selected for the source. -/
theorem secondBrokenEntry_partnerSpan_eq_chord
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    (vertex B.secondBase B.secondWord
        (B.secondChordPos (B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second
            (B.secondSourceEntry s hs)))))⁻¹ *
      vertex B.secondBase B.secondWord
        (B.secondBrokenEntryConnectors hs).partnerEnd =
      (B.chord[B.brokenAssignment.second.partner s]'
        (B.brokenAssignment.second.partner_lt s hs)).val := by
  let t := HalfEntry.entrySource B.brokenAssignment.index.second
    (B.secondSourceEntry s hs)
  let ht := HalfEntry.entrySource_mem B.brokenAssignment.index.second
    (B.secondSourceEntry s hs)
  let E := B.secondBrokenEntryConnectors hs
  have h := B.secondBroken_partnerSpan_eq_chord ht
  change (vertex B.secondBase B.secondWord
      (B.secondChordPos (B.brokenAssignment.second.partner t)))⁻¹ *
    vertex B.secondBase B.secondWord E.partnerEnd =
      (B.chord[B.brokenAssignment.second.partner t]'_).val at h
  have hsource : t = s := B.secondSourceEntry_source s hs
  have hpartner : B.brokenAssignment.second.partner t =
      B.brokenAssignment.second.partner s := congrArg _ hsource
  change (vertex B.secondBase B.secondWord
      (B.secondChordPos (B.brokenAssignment.second.partner t)))⁻¹ *
    vertex B.secondBase B.secondWord E.partnerEnd = _
  calc
    _ = (B.chord[B.brokenAssignment.second.partner t]'_).val := h
    _ = (B.chord[B.brokenAssignment.second.partner s]'_).val := by
      rw [getElem_congr_idx hpartner]

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
