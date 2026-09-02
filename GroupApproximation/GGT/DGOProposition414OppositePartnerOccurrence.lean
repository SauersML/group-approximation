import GroupApproximation.GGT.DGOProposition414ChordWalkCoverage
import GroupApproximation.GGT.DGOProposition414GapIndex

/-!
# Opposite-half occurrences of charged chord partners

Cross-half separation says that a chord edge charged by one half is absent
from the opposite half's partner list.  The trimmed chord-walk covering theorem
then supplies an actual opposite-half child whose chord segment contains that
edge.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- A first-half selected partner has the source label on the underlying
forward chord edge. -/
theorem firstPartner_chordLetter_label
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    (B.chord[B.brokenAssignment.first.partner s]'
      (B.brokenAssignment.first.partner_lt s hs)).IsCompOf (P.label s) := by
  let y := B.brokenAssignment.first.partner s
  have hy : y < B.chord.length := B.brokenAssignment.first.partner_lt s hs
  have hwordLen : B.firstChordPos y < B.firstWord.length :=
    B.brokenAssignment.first.partner_pos_lt s hs
  have hletter :
      (B.firstWord[B.firstChordPos y]'hwordLen).IsCompOf (P.label s) :=
    B.brokenAssignment.first.partner_letter s hs
  have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have hEnd : B.refinedCut (B.secondSide + 2) ≤ P.word.length := by
    rw [hright]
    exact B.secondVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
  let q := B.chord.length - 1 - y
  have hq : q < B.chord.length := by dsimp [q]; omega
  have hpos : B.firstChordPos y =
      (B.refinedCut (B.secondSide + 2) -
        B.refinedCut (B.firstSide + 1)) + q := by
    simp [firstChordPos, firstArcLength, hleft, hright, q]
  have hhalf := getElem_firstHalf_chord P.word B.refinedCut hEnd B.chord hq
    (show (B.refinedCut (B.secondSide + 2) -
        B.refinedCut (B.firstSide + 1)) + q < B.firstWord.length by
      rw [← hpos]
      exact hwordLen)
  have hrev : ((revWord B.chord)[q]'(by
      rw [OsinComponents.length_revWord]
      exact hq)).IsCompOf (P.label s) := by
    have hletter' :
        ((firstHalf P.word B.refinedCut (B.firstSide + 1)
          (B.secondSide + 2) B.chord)[
            (B.refinedCut (B.secondSide + 2) -
              B.refinedCut (B.firstSide + 1)) + q]'(by
                rw [← hpos]
                simpa only [firstWord] using hwordLen)).IsCompOf (P.label s) := by
      simpa only [firstWord, hpos] using hletter
    exact Eq.mp (congrArg (fun z => z.IsCompOf (P.label s)) hhalf) hletter'
  have hqy : y = B.chord.length - 1 - q := by
    dsimp [q]
    omega
  exact (isCompOf_getElem_revWord' B.chord (P.label s)
    (by rw [OsinComponents.length_revWord]; exact hq) hy hqy).mp hrev

/-- A wrapped-half selected partner has the source label on its forward chord
edge. -/
theorem secondPartner_chordLetter_label
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    (B.chord[B.brokenAssignment.second.partner s]'
      (B.brokenAssignment.second.partner_lt s hs)).IsCompOf (P.label s) := by
  let y := B.brokenAssignment.second.partner s
  have hy : y < B.chord.length := B.brokenAssignment.second.partner_lt s hs
  have hwordLen : B.secondChordPos y < B.secondWord.length :=
    B.brokenAssignment.second.partner_pos_lt s hs
  have hletter :
      (B.secondWord[B.secondChordPos y]'hwordLen).IsCompOf (P.label s) :=
    B.brokenAssignment.second.partner_letter s hs
  have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have hStart : B.refinedCut (B.firstSide + 1) ≤ P.word.length := by
    rw [hleft]
    exact B.firstVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr
        (B.side_order.trans B.secondSide_lt)))
  have hpos : B.secondChordPos y =
      (P.word.length - B.refinedCut (B.secondSide + 2)) +
        B.refinedCut (B.firstSide + 1) + y := by
    simp [secondChordPos, secondArcLength, hleft, hright]
  have hhalf := getElem_secondHalf_chord P.word B.refinedCut hStart B.chord hy
    (show (P.word.length - B.refinedCut (B.secondSide + 2)) +
        B.refinedCut (B.firstSide + 1) + y < B.secondWord.length by
      rw [← hpos]
      exact hwordLen)
  have hletter' :
      ((secondHalf P.word B.refinedCut (B.firstSide + 1)
        (B.secondSide + 2) B.chord)[
          (P.word.length - B.refinedCut (B.secondSide + 2)) +
            B.refinedCut (B.firstSide + 1) + y]'(by
              rw [← hpos]
              simpa only [secondWord] using hwordLen)).IsCompOf (P.label s) := by
    simpa only [secondWord, hpos] using hletter
  change (B.chord[y]'hy).IsCompOf (P.label s)
  exact Eq.mp (congrArg (fun z => z.IsCompOf (P.label s)) hhalf) hletter'

/-- A first-half charge's chord coordinate does not occur in the opposite
wrapped-half partner list. -/
theorem firstPartner_not_mem_secondPartners
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    B.brokenAssignment.first.partner s ∉
      B.brokenAssignment.index.second.partners := by
  intro hmem
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hmem
  have hjSource : j < B.brokenAssignment.index.second.sources.length := by
    rw [← B.brokenAssignment.index.second.partner_length]
    exact hj
  obtain ⟨t, ht, _hsource, htPartner⟩ :=
    B.brokenAssignment.index.second.entries j hjSource
  have heq : B.brokenAssignment.first.partner s =
      B.brokenAssignment.second.partner t := by
    rw [List.getElem?_eq_getElem hj] at htPartner
    exact hget.symm.trans (Option.some.inj htPartner)
  have hlabel : P.label s = P.label t := by
    apply eq_of_isCompOf_of_isCompOf
      (B.firstPartner_chordLetter_label s hs)
    simpa only [← heq] using B.secondPartner_chordLetter_label t ht
  exact B.crossHalf_partner_ne_of_label_eq s t hs ht hlabel heq

/-- A wrapped-half charge's chord coordinate does not occur in the opposite
first-half partner list. -/
theorem secondPartner_not_mem_firstPartners
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    B.brokenAssignment.second.partner s ∉
      B.brokenAssignment.index.first.partners := by
  intro hmem
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hmem
  have hjSource : j < B.brokenAssignment.index.first.sources.length := by
    rw [← B.brokenAssignment.index.first.partner_length]
    exact hj
  obtain ⟨t, ht, _hsource, htPartner⟩ :=
    B.brokenAssignment.index.first.entries j hjSource
  have heq : B.brokenAssignment.first.partner t =
      B.brokenAssignment.second.partner s := by
    rw [List.getElem?_eq_getElem hj] at htPartner
    exact (hget.symm.trans (Option.some.inj htPartner)).symm
  have hlabel : P.label t = P.label s := by
    apply eq_of_isCompOf_of_isCompOf
      (B.firstPartner_chordLetter_label t ht)
    simpa only [heq] using B.secondPartner_chordLetter_label s hs
  exact B.crossHalf_partner_ne_of_label_eq t s ht hs hlabel heq

/-- Select an endpoint according to a possibly noncomputable orientation
predicate. -/
noncomputable def endpointByOrientation (forward : Prop)
    (whenForward whenBackward : ℕ) : ℕ := by
  classical
  exact if forward then whenForward else whenBackward

/-- Trimming the selected endpoint of each chord-walk segment according to an
arbitrary orientation preserves every edge absent from the partner list. -/
theorem exists_edgeBetween_orientedTrimmedChordWalk
    (xs : List ℕ) (initial terminal y : ℕ)
    (houter : EdgeBetween initial terminal y) (hnot : y ∉ xs)
    (forward : Fin (xs.length + 1) → Prop) :
    ∃ j : Fin (xs.length + 1),
      EdgeBetween
        (if h : j.val < xs.length then
          endpointByOrientation (forward j) (xs[j.val] + 1) xs[j.val]
        else terminal)
        (if h : 0 < j.val then
          endpointByOrientation (forward j) (xs[j.val - 1]'(by omega))
            (xs[j.val - 1]'(by omega) + 1)
        else initial) y := by
  classical
  obtain ⟨j, hj⟩ := exists_edgeBetween_chordWalk xs initial terminal y houter
  refine ⟨j, ?_⟩
  by_cases hf : forward j
  · by_cases hn : j.val < xs.length
    · have hne : y ≠ xs[j.val] := by
        intro heq
        exact hnot (heq ▸ List.getElem_mem hn)
      have hstart : chordWalkStart terminal xs j = xs[j.val] := by
        simp [chordWalkStart, hn]
      rw [hstart] at hj
      simpa [endpointByOrientation, hf, hn, chordWalkFinish] using
        edgeBetween_succ_left hj hne
    · simpa [endpointByOrientation, hf, hn, chordWalkStart,
        chordWalkFinish] using hj
  · by_cases hp : 0 < j.val
    · have hne : y ≠ xs[j.val - 1]'(by omega) := by
        intro heq
        exact hnot (heq ▸ List.getElem_mem (by omega))
      have hfinish : chordWalkFinish initial xs j =
          xs[j.val - 1]'(by omega) := by
        simp [chordWalkFinish, hp]
      rw [hfinish] at hj
      simpa [endpointByOrientation, hf, hp, chordWalkStart] using
        edgeBetween_succ_right hj hne
    · simpa [endpointByOrientation, hf, hp, chordWalkStart,
        chordWalkFinish] using hj

/-! ## Specialization of the trimmed walk to the canonical gap coordinates -/

theorem firstGapChordStart_eq_trimmedWalk
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    B.firstGapChordStart j =
      if h : j.val < B.brokenAssignment.index.first.partners.length then
        endpointByOrientation (B.firstGapRunsForward j)
          (B.brokenAssignment.index.first.partners[j.val] + 1)
          B.brokenAssignment.index.first.partners[j.val]
      else B.chord.length := by
  classical
  let A := B.brokenAssignment.index.first
  by_cases h : j.val < A.sources.length
  · have hpLen : j.val < A.partners.length := by rwa [A.partner_length]
    let e : Fin A.sources.length := ⟨j.val, h⟩
    have hp := HalfEntry.partner_getElem_eq_partner_entrySource A e
    rw [List.getElem?_eq_getElem hpLen] at hp
    have hpEq := Option.some.inj hp
    unfold firstGapChordStart
    rw [show HalfGap.nextEntry A j = some e by
      simp [HalfGap.nextEntry, A, e, h]]
    rw [dif_pos hpLen]
    simpa [endpointByOrientation, A, e] using hpEq.symm
  · have hpLen : ¬ j.val < A.partners.length := by
      rw [A.partner_length]
      exact h
    unfold firstGapChordStart
    rw [show HalfGap.nextEntry A j = none by
      simp [HalfGap.nextEntry, A, h]]
    rw [dif_neg hpLen]

theorem firstGapChordFinish_eq_walk
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    B.firstGapChordFinish j =
      if h : 0 < j.val then
        endpointByOrientation (B.firstGapRunsForward j)
          (B.brokenAssignment.index.first.partners[j.val - 1]'(by
            rw [B.brokenAssignment.index.first.partner_length]
            have hj := j.isLt
            simp only [GreedyHalfFamilyIndex.pieceCount] at hj
            omega))
          (B.brokenAssignment.index.first.partners[j.val - 1]'(by
            rw [B.brokenAssignment.index.first.partner_length]
            have hj := j.isLt
            simp only [GreedyHalfFamilyIndex.pieceCount] at hj
            omega) + 1)
      else 0 := by
  classical
  let A := B.brokenAssignment.index.first
  by_cases h : 0 < j.val
  · have hsLen : j.val - 1 < A.sources.length := by
      have hj := j.isLt
      change j.val < A.pieceCount at hj
      simp only [GreedyHalfFamilyIndex.pieceCount] at hj
      omega
    have hpLen : j.val - 1 < A.partners.length := by
      rwa [A.partner_length]
    let e : Fin A.sources.length := ⟨j.val - 1, hsLen⟩
    have hp := HalfEntry.partner_getElem_eq_partner_entrySource A e
    rw [List.getElem?_eq_getElem hpLen] at hp
    have hpEq := Option.some.inj hp
    unfold firstGapChordFinish
    rw [show HalfGap.previousEntry A j = some e by
      simp [HalfGap.previousEntry, A, e, h]]
    rw [dif_pos h]
    simpa [endpointByOrientation, A, e] using hpEq.symm
  · unfold firstGapChordFinish
    rw [show HalfGap.previousEntry A j = none by
      simp [HalfGap.previousEntry, A, h]]
    rw [dif_neg h]

theorem secondGapChordStart_eq_walk
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    B.secondGapChordStart j =
      if h : j.val < B.brokenAssignment.index.second.partners.length then
        endpointByOrientation (B.secondGapRunsForward j)
          (B.brokenAssignment.index.second.partners[j.val] + 1)
          B.brokenAssignment.index.second.partners[j.val]
      else 0 := by
  classical
  let A := B.brokenAssignment.index.second
  by_cases h : j.val < A.sources.length
  · have hpLen : j.val < A.partners.length := by rwa [A.partner_length]
    let e : Fin A.sources.length := ⟨j.val, h⟩
    have hp := HalfEntry.partner_getElem_eq_partner_entrySource A e
    rw [List.getElem?_eq_getElem hpLen] at hp
    have hpEq := Option.some.inj hp
    unfold secondGapChordStart
    rw [show HalfGap.nextEntry A j = some e by
      simp [HalfGap.nextEntry, A, e, h]]
    rw [dif_pos hpLen]
    simpa [endpointByOrientation, A, e] using hpEq.symm
  · have hpLen : ¬ j.val < A.partners.length := by
      rw [A.partner_length]
      exact h
    unfold secondGapChordStart
    rw [show HalfGap.nextEntry A j = none by
      simp [HalfGap.nextEntry, A, h]]
    rw [dif_neg hpLen]

theorem secondGapChordFinish_eq_trimmedWalk
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    B.secondGapChordFinish j =
      if h : 0 < j.val then
        endpointByOrientation (B.secondGapRunsForward j)
          (B.brokenAssignment.index.second.partners[j.val - 1]'(by
            have hj := j.isLt
            rw [B.brokenAssignment.index.second.partner_length]
            simp only [GreedyHalfFamilyIndex.pieceCount] at hj
            omega))
          (B.brokenAssignment.index.second.partners[j.val - 1]'(by
            have hj := j.isLt
            rw [B.brokenAssignment.index.second.partner_length]
            simp only [GreedyHalfFamilyIndex.pieceCount] at hj
            omega) + 1)
      else B.chord.length := by
  classical
  let A := B.brokenAssignment.index.second
  by_cases h : 0 < j.val
  · have hsLen : j.val - 1 < A.sources.length := by
      have hj := j.isLt
      change j.val < A.pieceCount at hj
      simp only [GreedyHalfFamilyIndex.pieceCount] at hj
      omega
    have hpLen : j.val - 1 < A.partners.length := by
      rwa [A.partner_length]
    let e : Fin A.sources.length := ⟨j.val - 1, hsLen⟩
    have hp := HalfEntry.partner_getElem_eq_partner_entrySource A e
    rw [List.getElem?_eq_getElem hpLen] at hp
    have hpEq := Option.some.inj hp
    unfold secondGapChordFinish
    rw [show HalfGap.previousEntry A j = some e by
      simp [HalfGap.previousEntry, A, e, h]]
    rw [dif_pos h]
    simpa [endpointByOrientation, A, e] using hpEq.symm
  · unfold secondGapChordFinish
    rw [show HalfGap.previousEntry A j = none by
      simp [HalfGap.previousEntry, A, h]]
    rw [dif_neg h]

/-- Every first-half broken partner occurs on the chord of a concrete
wrapped-half child. -/
theorem exists_secondGap_containing_firstPartner
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    ∃ j : Fin B.brokenAssignment.index.second.pieceCount,
      EdgeBetween (B.secondGapChordStart j) (B.secondGapChordFinish j)
        (B.brokenAssignment.first.partner s) := by
  classical
  let y := B.brokenAssignment.first.partner s
  let toGap :
      Fin (B.brokenAssignment.index.second.partners.length + 1) →
        Fin B.brokenAssignment.index.second.pieceCount := fun j =>
    ⟨j.val, by
      simpa [GreedyHalfFamilyIndex.pieceCount,
        B.brokenAssignment.index.second.partner_length] using j.isLt⟩
  obtain ⟨j, hj⟩ := exists_edgeBetween_orientedTrimmedChordWalk
    B.brokenAssignment.index.second.partners B.chord.length 0 y
    (by simp [EdgeBetween, y, B.brokenAssignment.first.partner_lt s hs])
    (B.firstPartner_not_mem_secondPartners s hs)
    (fun j => B.secondGapRunsForward (toGap j))
  refine ⟨toGap j, ?_⟩
  rw [B.secondGapChordStart_eq_walk,
    B.secondGapChordFinish_eq_trimmedWalk]
  simpa [toGap] using hj

/-- Every wrapped-half broken partner occurs on the chord of a concrete
first-half child. -/
theorem exists_firstGap_containing_secondPartner
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    ∃ j : Fin B.brokenAssignment.index.first.pieceCount,
      EdgeBetween (B.firstGapChordStart j) (B.firstGapChordFinish j)
        (B.brokenAssignment.second.partner s) := by
  classical
  let y := B.brokenAssignment.second.partner s
  let toGap :
      Fin (B.brokenAssignment.index.first.partners.length + 1) →
        Fin B.brokenAssignment.index.first.pieceCount := fun j =>
    ⟨j.val, by
    simpa [GreedyHalfFamilyIndex.pieceCount,
      B.brokenAssignment.index.first.partner_length] using j.isLt⟩
  obtain ⟨j, hj⟩ := exists_edgeBetween_orientedTrimmedChordWalk
    B.brokenAssignment.index.first.partners 0 B.chord.length y
    (by simp [EdgeBetween, y, B.brokenAssignment.second.partner_lt s hs])
    (B.secondPartner_not_mem_firstPartners s hs)
    (fun j => B.firstGapRunsForward (toGap j))
  refine ⟨toGap j, ?_⟩
  rw [B.firstGapChordStart_eq_trimmedWalk,
    B.firstGapChordFinish_eq_walk]
  simpa [toGap] using hj

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
