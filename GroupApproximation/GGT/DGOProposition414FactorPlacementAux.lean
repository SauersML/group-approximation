import GroupApproximation.GGT.DGOProposition414GapBrokenFactors

/-!
# Distributed factor placement for DGO Proposition 4.14

This module assembles the surviving-component and broken-component target
slots produced by balanced surgery.  It proves the two-half distributed
factor placement required in the bisection step of
Dahmani--Guirardel--Osin Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

theorem mem_targetSlotPacket_iff
    {D : RelGenSet G Λ} {b : ℝ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D b index} {lam : Λ}
    (q : Sum (Fin index.first.pieceCount) (Fin index.second.pieceCount))
    (o : Option (TwoHalfTargetSlot A lam)) (x : ℕ) :
    x ∈ targetSlotPacket q o ↔
      ∃ X : TwoHalfTargetSlot A lam,
        o = some X ∧ X.child = q ∧ X.targetIndex = x := by
  classical
  cases o with
  | none => simp [targetSlotPacket]
  | some X =>
      by_cases hchild : X.child = q
      · simp [targetSlotPacket, hchild, eq_comm]
      · simp [targetSlotPacket, hchild]

/-- Conditional singleton packets indexed by different children are disjoint. -/
theorem conditionalSingletonPackets_disjoint
    {ι : Type*} [DecidableEq ι] (i j q : ι) (x y : ℕ) (hij : i ≠ j) :
    Disjoint (if i = q then ({x} : Finset ℕ) else ∅)
      (if j = q then ({y} : Finset ℕ) else ∅) := by
  by_cases hi : i = q
  · have hj : j ≠ q := by
      intro hj
      exact hij (hi.trans hj.symm)
    simp [hi, hj]
  · simp [hi]

theorem signedOptionalTargetSlotSpan_false
    {D : RelGenSet G Λ} {b : ℝ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D b index} {lam : Λ}
    (o : Option (TwoHalfTargetSlot A lam)) :
    signedOptionalTargetSlotSpan False o = optionalTargetSlotSpan o := by
  classical
  unfold signedOptionalTargetSlotSpan
  rw [if_neg not_false]

theorem signedOptionalTargetSlotSpan_none
    {D : RelGenSet G Λ} {b : ℝ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D b index} {lam : Λ}
    (inverted : Prop) :
    signedOptionalTargetSlotSpan (A := A) (lam := lam) inverted none = 1 := by
  classical
  unfold signedOptionalTargetSlotSpan
  by_cases h : inverted <;> simp [h, optionalTargetSlotSpan]

/-- The three child-side factors assigned to one parent target. -/
structure SourceDistributedFactors
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B) (s : ℕ) where
  leftSlot : Option (TwoHalfTargetSlot
    (B.gapIntervalsOfConfigurations C).toPathInput.family (P.label s))
  middleSlot : Option (TwoHalfTargetSlot
    (B.gapIntervalsOfConfigurations C).toPathInput.family (P.label s))
  rightSlot : Option (TwoHalfTargetSlot
    (B.gapIntervalsOfConfigurations C).toPathInput.family (P.label s))
  leftInverted : Prop
  middleInverted : Prop
  rightInverted : Prop
  factorization : P.span s =
    signedOptionalTargetSlotSpan leftInverted leftSlot *
      signedOptionalTargetSlotSpan middleInverted middleSlot *
      signedOptionalTargetSlotSpan rightInverted rightSlot

/-- A first-half broken component is the product of its entry slot, signed
opposite-half chord slot, and exit slot. -/
theorem firstBroken_slot_factorization
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    P.span s =
      signedOptionalTargetSlotSpan False (B.firstBrokenStartSlot C hs) *
        signedOptionalTargetSlotSpan (B.firstBrokenMiddleInverted hs)
          (B.firstBrokenMiddleSlot C hs) *
        signedOptionalTargetSlotSpan False (B.firstBrokenEndSlot C hs) := by
  classical
  let E := B.firstBrokenEntryConnectors hs
  have hsource := B.firstBrokenEntry_sourceSpan_eq hs
  rw [E.sourceSpan_three_factorization] at hsource
  have hpartner := B.firstBrokenEntry_partnerSpan_eq_chordInv hs
  let y : G :=
    (vertex B.firstBase B.firstWord
      (B.firstChordPos (B.brokenAssignment.first.partner
        (HalfEntry.entrySource B.brokenAssignment.index.first
          (B.firstSourceEntry s hs)))))⁻¹ *
      vertex B.firstBase B.firstWord E.partnerEnd
  change P.span s = RelLetter.listVal E.startConnector * y *
    (RelLetter.listVal E.endConnector)⁻¹ at hsource
  change y = (B.chord[B.brokenAssignment.first.partner s]'
    (B.brokenAssignment.first.partner_lt s hs)).val⁻¹ at hpartner
  rw [signedOptionalTargetSlotSpan_false,
    signedOptionalTargetSlotSpan_false]
  by_cases hentry : B.firstBrokenEntryForward hs
  · by_cases hexit : B.firstBrokenExitForward hs
    · have hmiddle : B.firstBrokenMiddleSlot C hs =
          some (B.firstBrokenPartnerSlot C hs) := by
        have hsame : B.firstBrokenEntryForward hs ↔
            B.firstBrokenExitForward hs :=
          ⟨fun _ => hexit, fun _ => hentry⟩
        unfold firstBrokenMiddleSlot
        rw [if_pos hsame]
      have hmiddleValue :
          signedOptionalTargetSlotSpan (B.firstBrokenMiddleInverted hs)
              (some (B.firstBrokenPartnerSlot C hs)) = y := by
        by_cases horient : B.secondGapChordStart
            (B.firstPartnerSecondGapOwner s) ≤
              B.secondGapChordFinish (B.firstPartnerSecondGapOwner s)
        · have hinv : B.firstBrokenMiddleInverted hs := by
            unfold firstBrokenMiddleInverted
            exact ⟨fun _ => horient, fun _ => hentry⟩
          unfold signedOptionalTargetSlotSpan
          rw [if_pos hinv]
          rw [B.firstBrokenPartnerSlot_span C hs, if_pos horient]
          exact hpartner.symm
        · have hinv : ¬ B.firstBrokenMiddleInverted hs := by
            unfold firstBrokenMiddleInverted
            intro hiff
            exact horient (hiff.mp hentry)
          unfold signedOptionalTargetSlotSpan
          rw [if_neg hinv]
          rw [B.firstBrokenPartnerSlot_span C hs, if_neg horient]
          exact hpartner.symm
      rw [(B.firstBrokenStartSlot_span_cases C hs).1 hentry,
        (B.firstBrokenEndSlot_span_cases C hs).1 hexit, hmiddle,
        hmiddleValue]
      exact hsource
    · have hmiddle : B.firstBrokenMiddleSlot C hs = none := by
        have hdiffer : ¬ (B.firstBrokenEntryForward hs ↔
            B.firstBrokenExitForward hs) := by
          intro hiff
          exact hexit (hiff.mp hentry)
        unfold firstBrokenMiddleSlot
        rw [if_neg hdiffer]
      rw [(B.firstBrokenStartSlot_span_cases C hs).1 hentry,
        (B.firstBrokenEndSlot_span_cases C hs).2 hexit, hmiddle]
      rw [signedOptionalTargetSlotSpan_none]
      simp only [mul_one]
      rw [E.endThroughPartner_value_factorization]
      change P.span s = RelLetter.listVal E.startConnector *
        (RelLetter.listVal E.endConnector * y⁻¹)⁻¹
      rw [hsource]
      group
  · by_cases hexit : B.firstBrokenExitForward hs
    · have hmiddle : B.firstBrokenMiddleSlot C hs = none := by
        have hdiffer : ¬ (B.firstBrokenEntryForward hs ↔
            B.firstBrokenExitForward hs) := by
          intro hiff
          exact hentry (hiff.mpr hexit)
        unfold firstBrokenMiddleSlot
        rw [if_neg hdiffer]
      rw [(B.firstBrokenStartSlot_span_cases C hs).2 hentry,
        (B.firstBrokenEndSlot_span_cases C hs).1 hexit, hmiddle]
      rw [signedOptionalTargetSlotSpan_none]
      simp only [mul_one]
      rw [E.startThroughPartner_value_factorization]
      change P.span s =
        (RelLetter.listVal E.startConnector * y) *
          (RelLetter.listVal E.endConnector)⁻¹
      exact hsource
    · have hmiddle : B.firstBrokenMiddleSlot C hs =
          some (B.firstBrokenPartnerSlot C hs) := by
        have hsame : B.firstBrokenEntryForward hs ↔
            B.firstBrokenExitForward hs := by
          constructor
          · intro he
            exact (hentry he).elim
          · intro he
            exact (hexit he).elim
        unfold firstBrokenMiddleSlot
        rw [if_pos hsame]
      have hmiddleValue :
          signedOptionalTargetSlotSpan (B.firstBrokenMiddleInverted hs)
              (some (B.firstBrokenPartnerSlot C hs)) = y⁻¹ := by
        by_cases horient : B.secondGapChordStart
            (B.firstPartnerSecondGapOwner s) ≤
              B.secondGapChordFinish (B.firstPartnerSecondGapOwner s)
        · have hinv : ¬ B.firstBrokenMiddleInverted hs := by
            unfold firstBrokenMiddleInverted
            intro hiff
            exact hentry (hiff.mpr horient)
          unfold signedOptionalTargetSlotSpan
          rw [if_neg hinv]
          rw [B.firstBrokenPartnerSlot_span C hs, if_pos horient,
            hpartner, inv_inv]
        · have hinv : B.firstBrokenMiddleInverted hs := by
            unfold firstBrokenMiddleInverted
            constructor
            · intro he
              exact (hentry he).elim
            · intro ho
              exact (horient ho).elim
          unfold signedOptionalTargetSlotSpan
          rw [if_pos hinv]
          rw [B.firstBrokenPartnerSlot_span C hs, if_neg horient,
            hpartner]
      rw [(B.firstBrokenStartSlot_span_cases C hs).2 hentry,
        (B.firstBrokenEndSlot_span_cases C hs).2 hexit, hmiddle,
        hmiddleValue, E.startThroughPartner_value_factorization,
        E.endThroughPartner_value_factorization]
      change P.span s = (RelLetter.listVal E.startConnector * y) * y⁻¹ *
        (RelLetter.listVal E.endConnector * y⁻¹)⁻¹
      rw [hsource]
      group

/-- A wrapped-half broken component has the analogous signed three-slot
factorization. -/
theorem secondBroken_slot_factorization
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    P.span s =
      signedOptionalTargetSlotSpan False (B.secondBrokenStartSlot C hs) *
        signedOptionalTargetSlotSpan (B.secondBrokenMiddleInverted hs)
          (B.secondBrokenMiddleSlot C hs) *
        signedOptionalTargetSlotSpan False (B.secondBrokenEndSlot C hs) := by
  classical
  let E := B.secondBrokenEntryConnectors hs
  have hsource := B.secondBrokenEntry_sourceSpan_eq hs
  rw [E.sourceSpan_three_factorization] at hsource
  have hpartner := B.secondBrokenEntry_partnerSpan_eq_chord hs
  let y : G :=
    (vertex B.secondBase B.secondWord
      (B.secondChordPos (B.brokenAssignment.second.partner
        (HalfEntry.entrySource B.brokenAssignment.index.second
          (B.secondSourceEntry s hs)))))⁻¹ *
      vertex B.secondBase B.secondWord E.partnerEnd
  change P.span s = RelLetter.listVal E.startConnector * y *
    (RelLetter.listVal E.endConnector)⁻¹ at hsource
  change y = (B.chord[B.brokenAssignment.second.partner s]'
    (B.brokenAssignment.second.partner_lt s hs)).val at hpartner
  rw [signedOptionalTargetSlotSpan_false,
    signedOptionalTargetSlotSpan_false]
  by_cases hentry : B.secondBrokenEntryForward hs
  · by_cases hexit : B.secondBrokenExitForward hs
    · have hmiddle : B.secondBrokenMiddleSlot C hs =
          some (B.secondBrokenPartnerSlot C hs) := by
        have hsame : B.secondBrokenEntryForward hs ↔
            B.secondBrokenExitForward hs :=
          ⟨fun _ => hexit, fun _ => hentry⟩
        unfold secondBrokenMiddleSlot
        rw [if_pos hsame]
      have hmiddleValue :
          signedOptionalTargetSlotSpan (B.secondBrokenMiddleInverted hs)
              (some (B.secondBrokenPartnerSlot C hs)) = y⁻¹ := by
        by_cases horient : B.firstGapChordStart
            (B.secondPartnerFirstGapOwner s) ≤
              B.firstGapChordFinish (B.secondPartnerFirstGapOwner s)
        · have hinv : B.secondBrokenMiddleInverted hs := by
            unfold secondBrokenMiddleInverted
            exact ⟨fun _ => horient, fun _ => hentry⟩
          unfold signedOptionalTargetSlotSpan
          rw [if_pos hinv]
          rw [B.secondBrokenPartnerSlot_span C hs, if_pos horient,
            ← hpartner]
        · have hinv : ¬ B.secondBrokenMiddleInverted hs := by
            unfold secondBrokenMiddleInverted
            intro hiff
            exact horient (hiff.mp hentry)
          unfold signedOptionalTargetSlotSpan
          rw [if_neg hinv]
          rw [B.secondBrokenPartnerSlot_span C hs, if_neg horient,
            ← hpartner]
      rw [(B.secondBrokenStartSlot_span_cases C hs).1 hentry,
        (B.secondBrokenEndSlot_span_cases C hs).1 hexit, hmiddle,
        hmiddleValue, E.startThroughPartner_value_factorization,
        E.endThroughPartner_value_factorization]
      change P.span s = (RelLetter.listVal E.startConnector * y) * y⁻¹ *
        (RelLetter.listVal E.endConnector * y⁻¹)⁻¹
      rw [hsource]
      group
    · have hmiddle : B.secondBrokenMiddleSlot C hs = none := by
        have hdiffer : ¬ (B.secondBrokenEntryForward hs ↔
            B.secondBrokenExitForward hs) := by
          intro hiff
          exact hexit (hiff.mp hentry)
        unfold secondBrokenMiddleSlot
        rw [if_neg hdiffer]
      rw [(B.secondBrokenStartSlot_span_cases C hs).1 hentry,
        (B.secondBrokenEndSlot_span_cases C hs).2 hexit, hmiddle]
      rw [signedOptionalTargetSlotSpan_none]
      simp only [mul_one]
      rw [E.startThroughPartner_value_factorization]
      change P.span s = (RelLetter.listVal E.startConnector * y) *
        (RelLetter.listVal E.endConnector)⁻¹
      exact hsource
  · by_cases hexit : B.secondBrokenExitForward hs
    · have hmiddle : B.secondBrokenMiddleSlot C hs = none := by
        have hdiffer : ¬ (B.secondBrokenEntryForward hs ↔
            B.secondBrokenExitForward hs) := by
          intro hiff
          exact hentry (hiff.mpr hexit)
        unfold secondBrokenMiddleSlot
        rw [if_neg hdiffer]
      rw [(B.secondBrokenStartSlot_span_cases C hs).2 hentry,
        (B.secondBrokenEndSlot_span_cases C hs).1 hexit, hmiddle]
      rw [signedOptionalTargetSlotSpan_none]
      simp only [mul_one]
      rw [E.endThroughPartner_value_factorization]
      change P.span s = RelLetter.listVal E.startConnector *
        (RelLetter.listVal E.endConnector * y⁻¹)⁻¹
      rw [hsource]
      group
    · have hmiddle : B.secondBrokenMiddleSlot C hs =
          some (B.secondBrokenPartnerSlot C hs) := by
        have hsame : B.secondBrokenEntryForward hs ↔
            B.secondBrokenExitForward hs := by
          constructor
          · intro he
            exact (hentry he).elim
          · intro he
            exact (hexit he).elim
        unfold secondBrokenMiddleSlot
        rw [if_pos hsame]
      have hmiddleValue :
          signedOptionalTargetSlotSpan (B.secondBrokenMiddleInverted hs)
              (some (B.secondBrokenPartnerSlot C hs)) = y := by
        by_cases horient : B.firstGapChordStart
            (B.secondPartnerFirstGapOwner s) ≤
              B.firstGapChordFinish (B.secondPartnerFirstGapOwner s)
        · have hinv : ¬ B.secondBrokenMiddleInverted hs := by
            unfold secondBrokenMiddleInverted
            intro hiff
            exact hentry (hiff.mpr horient)
          unfold signedOptionalTargetSlotSpan
          rw [if_neg hinv]
          rw [B.secondBrokenPartnerSlot_span C hs, if_pos horient,
            ← hpartner]
        · have hinv : B.secondBrokenMiddleInverted hs := by
            unfold secondBrokenMiddleInverted
            constructor
            · intro he
              exact (hentry he).elim
            · intro ho
              exact (horient ho).elim
          unfold signedOptionalTargetSlotSpan
          rw [if_pos hinv]
          rw [B.secondBrokenPartnerSlot_span C hs, if_neg horient,
            inv_inv, ← hpartner]
      rw [(B.secondBrokenStartSlot_span_cases C hs).2 hentry,
        (B.secondBrokenEndSlot_span_cases C hs).2 hexit, hmiddle,
        hmiddleValue]
      exact hsource

/-! ## Canonical factors of every parent target -/

/-- Entry factor chosen by the half containing the parent target. -/
noncomputable def distributedLeftSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B) (s : ℕ) :
    Option (TwoHalfTargetSlot
      (B.gapIntervalsOfConfigurations C).toPathInput.family (P.label s)) := by
  classical
  if hs : s ∈ B.componentPlacement.firstTarget then
    if hsurvives : B.componentPlacement.firstSurvives s then
      exact none
    else
      exact B.firstBrokenStartSlot C
        (mem_brokenSet_iff.mpr ⟨hs, hsurvives⟩)
  else if ht : s ∈ B.componentPlacement.secondTarget then
    if hsurvives : B.componentPlacement.secondSurvives s then
      exact none
    else
      exact B.secondBrokenStartSlot C
        (mem_brokenSet_iff.mpr ⟨ht, hsurvives⟩)
  else
    exact none

/-- Surviving sources use their inherited side; broken sources use the
opposite-half chord factor exactly when the two adjacent orientations agree. -/
noncomputable def distributedMiddleSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B) (s : ℕ) :
    Option (TwoHalfTargetSlot
      (B.gapIntervalsOfConfigurations C).toPathInput.family (P.label s)) := by
  classical
  if hs : s ∈ B.componentPlacement.firstTarget then
    if hsurvives : B.componentPlacement.firstSurvives s then
      exact some (B.firstSurvivorSlot C hs hsurvives)
    else
      exact B.firstBrokenMiddleSlot C
        (mem_brokenSet_iff.mpr ⟨hs, hsurvives⟩)
  else if ht : s ∈ B.componentPlacement.secondTarget then
    if hsurvives : B.componentPlacement.secondSurvives s then
      exact some (B.secondSurvivorSlot C ht hsurvives)
    else
      exact B.secondBrokenMiddleSlot C
        (mem_brokenSet_iff.mpr ⟨ht, hsurvives⟩)
  else
    exact none

/-- Exit factor chosen by the half containing the parent target. -/
noncomputable def distributedRightSlot
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B) (s : ℕ) :
    Option (TwoHalfTargetSlot
      (B.gapIntervalsOfConfigurations C).toPathInput.family (P.label s)) := by
  classical
  if hs : s ∈ B.componentPlacement.firstTarget then
    if hsurvives : B.componentPlacement.firstSurvives s then
      exact none
    else
      exact B.firstBrokenEndSlot C
        (mem_brokenSet_iff.mpr ⟨hs, hsurvives⟩)
  else if ht : s ∈ B.componentPlacement.secondTarget then
    if hsurvives : B.componentPlacement.secondSurvives s then
      exact none
    else
      exact B.secondBrokenEndSlot C
        (mem_brokenSet_iff.mpr ⟨ht, hsurvives⟩)
  else
    exact none

/-- The only nontrivial sign is the broken middle chord factor. -/
noncomputable def distributedMiddleInverted
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (s : ℕ) : Prop := by
  classical
  exact if hs : s ∈ B.componentPlacement.firstTarget then
    if hsurvives : B.componentPlacement.firstSurvives s then False
    else B.firstBrokenMiddleInverted
      (mem_brokenSet_iff.mpr ⟨hs, hsurvives⟩)
  else if ht : s ∈ B.componentPlacement.secondTarget then
    if hsurvives : B.componentPlacement.secondSurvives s then False
    else B.secondBrokenMiddleInverted
      (mem_brokenSet_iff.mpr ⟨ht, hsurvives⟩)
  else False

/-- Union of the three canonical factor packets of one parent source. -/
noncomputable def distributedPacket
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (q : Sum (Fin B.brokenAssignment.index.first.pieceCount)
      (Fin B.brokenAssignment.index.second.pieceCount)) (s : ℕ) : Finset ℕ :=
  (targetSlotPacket q (B.distributedLeftSlot C s) ∪
    targetSlotPacket q (B.distributedMiddleSlot C s)) ∪
      targetSlotPacket q (B.distributedRightSlot C s)

/-- The canonical three slots reproduce every original target span. -/
theorem distributedSlots_factorization
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ P.target) :
    P.span s =
      signedOptionalTargetSlotSpan False (B.distributedLeftSlot C s) *
        signedOptionalTargetSlotSpan (B.distributedMiddleInverted s)
          (B.distributedMiddleSlot C s) *
        signedOptionalTargetSlotSpan False (B.distributedRightSlot C s) := by
  classical
  have hcover := B.componentPlacement.target_cover
  rw [hcover] at hs
  rcases Finset.mem_union.mp hs with hsFirst | hsSecond
  · by_cases hsurvives : B.componentPlacement.firstSurvives s
    · simp only [distributedLeftSlot, distributedMiddleSlot,
        distributedRightSlot, distributedMiddleInverted, hsFirst,
        hsurvives, ↓reduceDIte, signedOptionalTargetSlotSpan_false,
        optionalTargetSlotSpan, one_mul, mul_one]
      exact (B.firstSurvivorSlot_span C hsFirst hsurvives).symm
    · let hbroken : s ∈ brokenSet B.componentPlacement.firstTarget
          B.componentPlacement.firstSurvives :=
        mem_brokenSet_iff.mpr ⟨hsFirst, hsurvives⟩
      simpa only [distributedLeftSlot, distributedMiddleSlot,
        distributedRightSlot, distributedMiddleInverted, hsFirst,
        hsurvives, ↓reduceDIte] using
        B.firstBroken_slot_factorization C hbroken
  · have hnotFirst : s ∉ B.componentPlacement.firstTarget := by
      intro hsFirst
      exact (Finset.disjoint_left.mp B.componentPlacement.target_disjoint)
        hsFirst hsSecond
    by_cases hsurvives : B.componentPlacement.secondSurvives s
    · simp only [distributedLeftSlot, distributedMiddleSlot,
        distributedRightSlot, distributedMiddleInverted, hnotFirst,
        hsSecond, hsurvives, ↓reduceDIte,
        signedOptionalTargetSlotSpan_false, optionalTargetSlotSpan,
        one_mul, mul_one]
      exact (B.secondSurvivorSlot_span C hsSecond hsurvives).symm
    · let hbroken : s ∈ brokenSet B.componentPlacement.secondTarget
          B.componentPlacement.secondSurvives :=
        mem_brokenSet_iff.mpr ⟨hsSecond, hsurvives⟩
      simpa only [distributedLeftSlot, distributedMiddleSlot,
        distributedRightSlot, distributedMiddleInverted, hnotFirst,
        hsSecond, hsurvives, ↓reduceDIte] using
        B.secondBroken_slot_factorization C hbroken

/-! ## Separation of the three factors of one source -/

/-- The three slots of a broken first-half source occupy its two adjacent
first-half connector blocks and, when present, one wrapped-half chord block. -/
theorem firstBroken_slots_disjoint
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives)
    (q : Sum (Fin B.brokenAssignment.index.first.pieceCount)
      (Fin B.brokenAssignment.index.second.pieceCount)) :
    Disjoint (targetSlotPacket q (B.firstBrokenStartSlot C hs))
        (targetSlotPacket q (B.firstBrokenMiddleSlot C hs)) ∧
      Disjoint
        (targetSlotPacket q (B.firstBrokenStartSlot C hs) ∪
          targetSlotPacket q (B.firstBrokenMiddleSlot C hs))
        (targetSlotPacket q (B.firstBrokenEndSlot C hs)) := by
  classical
  let e := B.firstSourceEntry s hs
  let j₀ := HalfEntry.entryChild B.brokenAssignment.index.first e
  let j₁ := HalfEntry.exitChild B.brokenAssignment.index.first e
  have hchildren :
      HalfEntry.entryChild B.brokenAssignment.index.first e ≠
        HalfEntry.exitChild B.brokenAssignment.index.first e :=
    HalfEntry.entryChild_ne_exitChild _ _
  cases q <;>
    by_cases hstart : 0 < (B.firstGapRight j₀).length <;>
    by_cases hend : 0 < (B.firstGapLeft j₁).length <;>
    by_cases hmiddle : B.firstBrokenEntryForward hs ↔
      B.firstBrokenExitForward hs <;>
    simp_all [firstBrokenStartSlot, firstBrokenEndSlot,
      firstBrokenMiddleSlot, e, j₀, j₁, targetSlotPacket,
      conditionalSingletonPackets_disjoint,
      TwoHalfPathInput.firstEntryStartConnectorSlot,
      TwoHalfPathInput.firstEntryEndConnectorSlot,
      TwoHalfPathInput.firstRightConnectorSlot,
      TwoHalfPathInput.firstLeftConnectorSlot,
      TwoHalfPathInput.firstTargetSlot]

/-- Wrapped-half counterpart of `firstBroken_slots_disjoint`. -/
theorem secondBroken_slots_disjoint
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives)
    (q : Sum (Fin B.brokenAssignment.index.first.pieceCount)
      (Fin B.brokenAssignment.index.second.pieceCount)) :
    Disjoint (targetSlotPacket q (B.secondBrokenStartSlot C hs))
        (targetSlotPacket q (B.secondBrokenMiddleSlot C hs)) ∧
      Disjoint
        (targetSlotPacket q (B.secondBrokenStartSlot C hs) ∪
          targetSlotPacket q (B.secondBrokenMiddleSlot C hs))
        (targetSlotPacket q (B.secondBrokenEndSlot C hs)) := by
  classical
  let e := B.secondSourceEntry s hs
  let j₀ := HalfEntry.entryChild B.brokenAssignment.index.second e
  let j₁ := HalfEntry.exitChild B.brokenAssignment.index.second e
  have hchildren :
      HalfEntry.entryChild B.brokenAssignment.index.second e ≠
        HalfEntry.exitChild B.brokenAssignment.index.second e :=
    HalfEntry.entryChild_ne_exitChild _ _
  cases q <;>
    by_cases hstart : 0 < (B.secondGapRight j₀).length <;>
    by_cases hend : 0 < (B.secondGapLeft j₁).length <;>
    by_cases hmiddle : B.secondBrokenEntryForward hs ↔
      B.secondBrokenExitForward hs <;>
    simp_all [secondBrokenStartSlot, secondBrokenEndSlot,
      secondBrokenMiddleSlot, e, j₀, j₁, targetSlotPacket,
      conditionalSingletonPackets_disjoint,
      TwoHalfPathInput.secondEntryStartConnectorSlot,
      TwoHalfPathInput.secondEntryEndConnectorSlot,
      TwoHalfPathInput.secondRightConnectorSlot,
      TwoHalfPathInput.secondLeftConnectorSlot,
      TwoHalfPathInput.secondTargetSlot]

/-- The canonical slots of any one parent target are pairwise disjoint in
each child. -/
theorem distributedSlots_disjoint
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (q : Sum (Fin B.brokenAssignment.index.first.pieceCount)
      (Fin B.brokenAssignment.index.second.pieceCount))
    (hs : s ∈ P.target) :
    Disjoint (targetSlotPacket q (B.distributedLeftSlot C s))
        (targetSlotPacket q (B.distributedMiddleSlot C s)) ∧
      Disjoint
        (targetSlotPacket q (B.distributedLeftSlot C s) ∪
          targetSlotPacket q (B.distributedMiddleSlot C s))
        (targetSlotPacket q (B.distributedRightSlot C s)) := by
  classical
  have hcover := B.componentPlacement.target_cover
  rw [hcover] at hs
  rcases Finset.mem_union.mp hs with hsFirst | hsSecond
  · by_cases hsurvives : B.componentPlacement.firstSurvives s
    · simp [distributedLeftSlot, distributedMiddleSlot,
        distributedRightSlot, hsFirst, hsurvives, targetSlotPacket]
    · let hbroken : s ∈ brokenSet B.componentPlacement.firstTarget
          B.componentPlacement.firstSurvives :=
        mem_brokenSet_iff.mpr ⟨hsFirst, hsurvives⟩
      simpa only [distributedLeftSlot, distributedMiddleSlot,
        distributedRightSlot, hsFirst, hsurvives, ↓reduceDIte] using
        B.firstBroken_slots_disjoint C hbroken q
  · have hnotFirst : s ∉ B.componentPlacement.firstTarget := by
      intro hsFirst
      exact (Finset.disjoint_left.mp B.componentPlacement.target_disjoint)
        hsFirst hsSecond
    by_cases hsurvives : B.componentPlacement.secondSurvives s
    · simp [distributedLeftSlot, distributedMiddleSlot,
        distributedRightSlot, hnotFirst, hsSecond, hsurvives,
        targetSlotPacket]
    · let hbroken : s ∈ brokenSet B.componentPlacement.secondTarget
          B.componentPlacement.secondSurvives :=
        mem_brokenSet_iff.mpr ⟨hsSecond, hsurvives⟩
      simpa only [distributedLeftSlot, distributedMiddleSlot,
        distributedRightSlot, hnotFirst, hsSecond, hsurvives,
        ↓reduceDIte] using B.secondBroken_slots_disjoint C hbroken q

/-! ## First-family coordinate origins -/

theorem halfEntry_exitChild_injective
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L) {e f : Fin A.sources.length}
    (h : HalfEntry.exitChild A e = HalfEntry.exitChild A f) : e = f := by
  apply Fin.ext
  have hval := congrArg Fin.val h
  change e.val + 1 = f.val + 1 at hval
  omega

/-- The four separated target blocks which can charge a first-family child. -/
inductive FirstChildSlotKind
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (s : ℕ) : Type
  | endConnector
      (hs : s ∈ brokenSet B.componentPlacement.firstTarget
        B.componentPlacement.firstSurvives)
      (present : 0 < (B.firstGapLeft
        (HalfEntry.exitChild B.brokenAssignment.index.first
          (B.firstSourceEntry s hs))).length)
  | survivor (hs : s ∈ B.componentPlacement.firstTarget)
      (hsurvives : B.componentPlacement.firstSurvives s)
  | startConnector
      (hs : s ∈ brokenSet B.componentPlacement.firstTarget
        B.componentPlacement.firstSurvives)
      (present : 0 < (B.firstGapRight (B.firstBrokenOwner s hs)).length)
  | chord
      (hs : s ∈ brokenSet B.componentPlacement.secondTarget
        B.componentPlacement.secondSurvives)

namespace FirstChildSlotKind

noncomputable def child
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (K : FirstChildSlotKind B s) :
    Fin B.brokenAssignment.index.first.pieceCount :=
  match K with
  | .endConnector hs _ => HalfEntry.exitChild B.brokenAssignment.index.first
      (B.firstSourceEntry s hs)
  | .survivor hs hsurvives => B.firstSurvivorGapOwner hs hsurvives
  | .startConnector hs _ => B.firstBrokenOwner s hs
  | .chord _ => B.secondPartnerFirstGapOwner s

noncomputable def targetIndex
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (K : FirstChildSlotKind B s) : ℕ :=
  match K with
  | .endConnector _ _ => 0
  | .survivor hs hsurvives => B.firstSurvivorLocalIndex hs hsurvives
  | .startConnector hs _ =>
      (B.firstGapLeft (B.firstBrokenOwner s hs)).length +
        (B.firstGapFinishSide (B.firstBrokenOwner s hs) -
          B.firstGapStartSide (B.firstBrokenOwner s hs))
  | .chord _ => B.firstGapChordTargetIndex
      (B.secondPartnerFirstGapOwner s)
      (B.brokenAssignment.second.partner s)

def region
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (K : FirstChildSlotKind B s) : ℕ :=
  match K with
  | .endConnector _ _ => 0
  | .survivor _ _ => 1
  | .startConnector _ _ => 2
  | .chord _ => 3

theorem targetIndex_lt_of_region_lt
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s t : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (K : FirstChildSlotKind B s) (L : FirstChildSlotKind B t)
    (hchild : K.child = L.child) (hregion : K.region < L.region) :
    K.targetIndex < L.targetIndex := by
  cases K <;> cases L <;> simp only [region] at hregion
  all_goals try omega
  all_goals simp only [child, targetIndex] at hchild ⊢
  · have hpositive := ‹0 < (B.firstGapLeft _).length›
    rw [hchild] at hpositive
    unfold firstSurvivorLocalIndex
    omega
  · have hpositive := ‹0 < (B.firstGapLeft _).length›
    rw [hchild] at hpositive
    omega
  · have hpositive := ‹0 < (B.firstGapLeft _).length›
    rw [hchild] at hpositive
    unfold firstGapChordTargetIndex auxiliaryChordTargetIndex
    omega
  · have hmem := Finset.mem_filter.mp
      (B.firstSurvivorGapOwner_mem ‹_› ‹_›)
    have hstartIndex := congrArg (fun j =>
      (B.firstGapLeft j).length +
        (B.firstGapFinishSide j - B.firstGapStartSide j)) hchild
    rw [← hstartIndex]
    unfold firstSurvivorLocalIndex
    omega
  · have hmem := Finset.mem_filter.mp
      (B.firstSurvivorGapOwner_mem ‹_› ‹_›)
    have hchordIndex := congrArg (fun j =>
      B.firstGapChordTargetIndex j
        (B.brokenAssignment.second.partner t)) hchild
    rw [← hchordIndex]
    unfold firstSurvivorLocalIndex firstGapChordTargetIndex
      auxiliaryChordTargetIndex
    omega
  · have hpositive := ‹0 < (B.firstGapRight _).length›
    have hchordIndex := congrArg (fun j =>
      B.firstGapChordTargetIndex j
        (B.brokenAssignment.second.partner t)) hchild
    rw [← hchordIndex]
    unfold firstGapChordTargetIndex auxiliaryChordTargetIndex
    omega

/-- In one first-family child, the block and local target coordinate determine
the original parent source. -/
theorem source_eq_of_same_coordinate
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s t : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (K : FirstChildSlotKind B s) (L : FirstChildSlotKind B t)
    (hchild : K.child = L.child)
    (hindex : K.targetIndex = L.targetIndex) : s = t := by
  have hregion : K.region = L.region := by
    apply Nat.le_antisymm
    · by_contra hnot
      have hlt : L.region < K.region := by omega
      have hstrict := L.targetIndex_lt_of_region_lt K hchild.symm hlt
      omega
    · by_contra hnot
      have hlt : K.region < L.region := by omega
      have hstrict := K.targetIndex_lt_of_region_lt L hchild hlt
      omega
  cases K <;> cases L <;> simp only [region] at hregion
  all_goals try omega
  all_goals simp only [child, targetIndex] at hchild hindex
  · have hentry := halfEntry_exitChild_injective
      B.brokenAssignment.index.first hchild
    calc
      s = HalfEntry.entrySource B.brokenAssignment.index.first
          (B.firstSourceEntry s ‹_›) := (B.firstSourceEntry_source s ‹_›).symm
      _ = HalfEntry.entrySource B.brokenAssignment.index.first
          (B.firstSourceEntry t ‹_›) := congrArg _ hentry
      _ = t := B.firstSourceEntry_source t ‹_›
  case survivor.survivor hsS hsurvivesS hsT hsurvivesT =>
    have hsMem : s ∈ B.firstGapArcSources
        (B.firstSurvivorGapOwner hsS hsurvivesS) :=
      B.firstSurvivorGapOwner_mem hsS hsurvivesS
    have htMem₀ : t ∈ B.firstGapArcSources
        (B.firstSurvivorGapOwner hsT hsurvivesT) :=
      B.firstSurvivorGapOwner_mem hsT hsurvivesT
    have htMem : t ∈ B.firstGapArcSources
        (B.firstSurvivorGapOwner hsS hsurvivesS) := by
      rw [hchild]
      exact htMem₀
    have hleft := congrArg
      (fun j => (B.firstGapLeft j).length) hchild
    have hstart := congrArg B.firstGapStartSide hchild
    apply B.firstGapArcSource_injective _ hsMem htMem
    unfold firstSurvivorLocalIndex at hindex
    omega
  · exact B.firstBrokenOwner_injective ‹_› ‹_› hchild
  · have hsMem : s ∈ B.firstGapChordSources
        (B.secondPartnerFirstGapOwner s) :=
      Finset.mem_filter.mpr ⟨‹_›, rfl⟩
    have htMem : t ∈ B.firstGapChordSources
        (B.secondPartnerFirstGapOwner s) := by
      apply Finset.mem_filter.mpr
      exact ⟨‹_›, hchild.symm⟩
    have hchordIndex := congrArg (fun j =>
      B.firstGapChordTargetIndex j
        (B.brokenAssignment.second.partner t)) hchild
    apply B.firstGapChordSource_injective _ hsMem htMem
    exact hindex.trans hchordIndex.symm

end FirstChildSlotKind

/-! ## Wrapped-family coordinate origins -/

/-- The four separated target blocks which can charge a wrapped-family child. -/
inductive SecondChildSlotKind
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (s : ℕ) : Type
  | endConnector
      (hs : s ∈ brokenSet B.componentPlacement.secondTarget
        B.componentPlacement.secondSurvives)
      (present : 0 < (B.secondGapLeft
        (HalfEntry.exitChild B.brokenAssignment.index.second
          (B.secondSourceEntry s hs))).length)
  | survivor (hs : s ∈ B.componentPlacement.secondTarget)
      (hsurvives : B.componentPlacement.secondSurvives s)
  | startConnector
      (hs : s ∈ brokenSet B.componentPlacement.secondTarget
        B.componentPlacement.secondSurvives)
      (present : 0 < (B.secondGapRight (B.secondBrokenOwner s hs)).length)
  | chord
      (hs : s ∈ brokenSet B.componentPlacement.firstTarget
        B.componentPlacement.firstSurvives)

namespace SecondChildSlotKind

noncomputable def child
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (K : SecondChildSlotKind B s) :
    Fin B.brokenAssignment.index.second.pieceCount :=
  match K with
  | .endConnector hs _ => HalfEntry.exitChild B.brokenAssignment.index.second
      (B.secondSourceEntry s hs)
  | .survivor hs hsurvives => B.secondSurvivorGapOwner hs hsurvives
  | .startConnector hs _ => B.secondBrokenOwner s hs
  | .chord _ => B.firstPartnerSecondGapOwner s

noncomputable def targetIndex
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (K : SecondChildSlotKind B s) : ℕ :=
  match K with
  | .endConnector _ _ => 0
  | .survivor hs hsurvives => B.secondSurvivorLocalIndex hs hsurvives
  | .startConnector hs _ =>
      (B.secondGapLeft (B.secondBrokenOwner s hs)).length +
        (B.secondGapFinishSide (B.secondBrokenOwner s hs) -
          B.secondGapStartSide (B.secondBrokenOwner s hs))
  | .chord _ => B.secondGapChordTargetIndex
      (B.firstPartnerSecondGapOwner s)
      (B.brokenAssignment.first.partner s)

def region
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (K : SecondChildSlotKind B s) : ℕ :=
  match K with
  | .endConnector _ _ => 0
  | .survivor _ _ => 1
  | .startConnector _ _ => 2
  | .chord _ => 3

theorem targetIndex_lt_of_region_lt
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s t : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (K : SecondChildSlotKind B s) (L : SecondChildSlotKind B t)
    (hchild : K.child = L.child) (hregion : K.region < L.region) :
    K.targetIndex < L.targetIndex := by
  cases K <;> cases L <;> simp only [region] at hregion
  all_goals try omega
  all_goals simp only [child, targetIndex] at hchild ⊢
  · have hpositive := ‹0 < (B.secondGapLeft _).length›
    rw [hchild] at hpositive
    unfold secondSurvivorLocalIndex
    omega
  · have hpositive := ‹0 < (B.secondGapLeft _).length›
    rw [hchild] at hpositive
    omega
  · have hpositive := ‹0 < (B.secondGapLeft _).length›
    rw [hchild] at hpositive
    unfold secondGapChordTargetIndex auxiliaryChordTargetIndex
    omega
  · have hmem := Finset.mem_filter.mp
      (B.secondSurvivorGapOwner_mem ‹_› ‹_›)
    have hstartIndex := congrArg (fun j =>
      (B.secondGapLeft j).length +
        (B.secondGapFinishSide j - B.secondGapStartSide j)) hchild
    rw [← hstartIndex]
    unfold secondSurvivorLocalIndex
    omega
  · have hmem := Finset.mem_filter.mp
      (B.secondSurvivorGapOwner_mem ‹_› ‹_›)
    have hchordIndex := congrArg (fun j =>
      B.secondGapChordTargetIndex j
        (B.brokenAssignment.first.partner t)) hchild
    rw [← hchordIndex]
    unfold secondSurvivorLocalIndex secondGapChordTargetIndex
      auxiliaryChordTargetIndex
    omega
  · have hpositive := ‹0 < (B.secondGapRight _).length›
    have hchordIndex := congrArg (fun j =>
      B.secondGapChordTargetIndex j
        (B.brokenAssignment.first.partner t)) hchild
    rw [← hchordIndex]
    unfold secondGapChordTargetIndex auxiliaryChordTargetIndex
    omega

/-- In one wrapped-family child, the block and local target coordinate
determine the original parent source. -/
theorem source_eq_of_same_coordinate
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s t : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (K : SecondChildSlotKind B s) (L : SecondChildSlotKind B t)
    (hchild : K.child = L.child)
    (hindex : K.targetIndex = L.targetIndex) : s = t := by
  have hregion : K.region = L.region := by
    apply Nat.le_antisymm
    · by_contra hnot
      have hlt : L.region < K.region := by omega
      have hstrict := L.targetIndex_lt_of_region_lt K hchild.symm hlt
      omega
    · by_contra hnot
      have hlt : K.region < L.region := by omega
      have hstrict := K.targetIndex_lt_of_region_lt L hchild hlt
      omega
  cases K <;> cases L <;> simp only [region] at hregion
  all_goals try omega
  all_goals simp only [child, targetIndex] at hchild hindex
  · have hentry := halfEntry_exitChild_injective
      B.brokenAssignment.index.second hchild
    calc
      s = HalfEntry.entrySource B.brokenAssignment.index.second
          (B.secondSourceEntry s ‹_›) := (B.secondSourceEntry_source s ‹_›).symm
      _ = HalfEntry.entrySource B.brokenAssignment.index.second
          (B.secondSourceEntry t ‹_›) := congrArg _ hentry
      _ = t := B.secondSourceEntry_source t ‹_›
  case survivor.survivor hsS hsurvivesS hsT hsurvivesT =>
    have hsMem : s ∈ B.secondGapArcSources
        (B.secondSurvivorGapOwner hsS hsurvivesS) :=
      B.secondSurvivorGapOwner_mem hsS hsurvivesS
    have htMem₀ : t ∈ B.secondGapArcSources
        (B.secondSurvivorGapOwner hsT hsurvivesT) :=
      B.secondSurvivorGapOwner_mem hsT hsurvivesT
    have htMem : t ∈ B.secondGapArcSources
        (B.secondSurvivorGapOwner hsS hsurvivesS) := by
      rw [hchild]
      exact htMem₀
    have hleft := congrArg
      (fun j => (B.secondGapLeft j).length) hchild
    have hstart := congrArg B.secondGapStartSide hchild
    apply B.secondGapArcSource_injective _ hsMem htMem
    unfold secondSurvivorLocalIndex at hindex
    omega
  · exact B.secondBrokenOwner_injective ‹_› ‹_› hchild
  · have hsMem : s ∈ B.secondGapChordSources
        (B.firstPartnerSecondGapOwner s) :=
      Finset.mem_filter.mpr ⟨‹_›, rfl⟩
    have htMem : t ∈ B.secondGapChordSources
        (B.firstPartnerSecondGapOwner s) := by
      apply Finset.mem_filter.mpr
      exact ⟨‹_›, hchild.symm⟩
    have hchordIndex := congrArg (fun j =>
      B.secondGapChordTargetIndex j
        (B.brokenAssignment.first.partner t)) hchild
    apply B.secondGapChordSource_injective _ hsMem htMem
    exact hindex.trans hchordIndex.symm

end SecondChildSlotKind

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
