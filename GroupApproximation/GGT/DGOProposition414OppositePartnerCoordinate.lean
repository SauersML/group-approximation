import GroupApproximation.GGT.DGOProposition414OppositePartnerOccurrence
import GroupApproximation.GGT.DGOProposition414OrientedSegment

/-!
# Local chord coordinates for opposite-half partner occurrences

An unoriented chord edge occurring between the endpoints of a child has a
canonical local position in that child's oriented chord word.  This file
turns the cross-half occurrence theorem into the actual child-side coordinate
needed by the distributed charging construction.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The local position of the forward edge `[y,y+1]` in the oriented segment
from `a` to `b`.  In the reverse orientation it is counted back from `a`. -/
def orientedEdgeIndex (a b y : ℕ) : ℕ :=
  if a ≤ b then y - a else a - (y + 1)

/-- Every edge between the endpoints gives a genuine letter position in the
oriented segment. -/
theorem orientedEdgeIndex_lt (word : List (RelLetter G Λ))
    {a b y : ℕ} (ha : a ≤ word.length) (hb : b ≤ word.length)
    (hedge : EdgeBetween a b y) :
    orientedEdgeIndex a b y < (orientedSegment word a b).length := by
  have hor := hedge
  unfold EdgeBetween at hor
  by_cases hab : a ≤ b
  · have hforward : a ≤ y ∧ y + 1 ≤ b := by omega
    rw [length_orientedSegment word ha hb]
    simp [orientedEdgeIndex, hab, Nat.dist_eq_sub_of_le hab]
    omega
  · have hba : b ≤ a := by omega
    have hreverse : b ≤ y ∧ y + 1 ≤ a := by omega
    rw [length_orientedSegment word ha hb, Nat.dist_comm,
      Nat.dist_eq_sub_of_le hba]
    simp [orientedEdgeIndex, hab]
    omega

/-- The canonical local position carries the same peripheral label as the
underlying forward chord edge, independently of segment orientation. -/
theorem orientedEdgeIndex_isCompOf
    (word : List (RelLetter G Λ)) (lam : Λ)
    {a b y : ℕ} (ha : a ≤ word.length) (hb : b ≤ word.length)
    (hy : y < word.length) (hedge : EdgeBetween a b y)
    (hlabel : (word[y]'hy).IsCompOf lam) :
    ((orientedSegment word a b)[orientedEdgeIndex a b y]'
      (orientedEdgeIndex_lt word ha hb hedge)).IsCompOf lam := by
  have hor := hedge
  unfold EdgeBetween at hor
  by_cases hab : a ≤ b
  · have hforward : a ≤ y ∧ y + 1 ≤ b := by omega
    simp only [orientedSegment, if_pos hab, orientedEdgeIndex]
    simpa only [List.getElem_take, List.getElem_drop, Nat.add_sub_of_le
      hforward.1] using hlabel
  · have hba : b ≤ a := by omega
    have hreverse : b ≤ y ∧ y + 1 ≤ a := by omega
    let segment := (word.drop b).take (a - b)
    have hsegmentLen : segment.length = a - b := by
      dsimp [segment]
      rw [List.length_take, List.length_drop]
      omega
    have hlocal : a - (y + 1) < segment.length := by
      rw [hsegmentLen]
      omega
    have hforwardIndex : y - b < segment.length := by
      rw [hsegmentLen]
      omega
    have hsegmentLabel :
        (segment[y - b]'hforwardIndex).IsCompOf lam := by
      dsimp [segment]
      simpa only [List.getElem_take, List.getElem_drop,
        Nat.add_sub_of_le hreverse.1] using hlabel
    have hreverseLabel :=
      (isCompOf_getElem_revWord' segment lam
        (by rw [OsinComponents.length_revWord]; exact hlocal)
        hforwardIndex (by rw [hsegmentLen]; omega)).mpr hsegmentLabel
    simpa only [orientedSegment, if_neg hab, orientedEdgeIndex,
      segment] using hreverseLabel

/-- Side index of a chord edge in an auxiliary interval. -/
def auxiliaryChordTargetIndex
    (left right : List (RelLetter G Λ)) (arcSides a b y : ℕ) : ℕ :=
  left.length + arcSides + right.length + orientedEdgeIndex a b y

/-- The chord-side coordinate lies in the complete side range of the child. -/
theorem auxiliaryChordTargetIndex_lt
    (word left right : List (RelLetter G Λ)) (arcSides : ℕ)
    {a b y : ℕ} (ha : a ≤ word.length) (hb : b ≤ word.length)
    (hedge : EdgeBetween a b y) :
    auxiliaryChordTargetIndex left right arcSides a b y <
      left.length + arcSides + right.length +
        (orientedSegment word a b).length := by
  unfold auxiliaryChordTargetIndex
  have hlt := orientedEdgeIndex_lt word ha hb hedge
  omega

namespace BalancedSplitData

theorem firstGapChordStart_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    B.firstGapChordStart j ≤ B.chord.length := by
  classical
  cases hnext : HalfGap.nextEntry B.brokenAssignment.index.first j with
  | none => simp [firstGapChordStart, hnext]
  | some e =>
      have hmem := HalfEntry.entrySource_mem
        B.brokenAssignment.index.first e
      have hlt := B.brokenAssignment.first.partner_lt
        (HalfEntry.entrySource B.brokenAssignment.index.first e) hmem
      simp only [firstGapChordStart, hnext]
      by_cases hf : B.firstGapRunsForward j
      · simp only [hf, ↓reduceIte]
        omega
      · simp only [hf, ↓reduceIte]
        omega

theorem firstGapChordFinish_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    B.firstGapChordFinish j ≤ B.chord.length := by
  classical
  cases hprev : HalfGap.previousEntry B.brokenAssignment.index.first j with
  | none => simp [firstGapChordFinish, hprev]
  | some e =>
      have hmem := HalfEntry.entrySource_mem
        B.brokenAssignment.index.first e
      have hlt := B.brokenAssignment.first.partner_lt
        (HalfEntry.entrySource B.brokenAssignment.index.first e) hmem
      simp only [firstGapChordFinish, hprev]
      by_cases hf : B.firstGapRunsForward j
      · simp only [hf, ↓reduceIte]
        omega
      · simp only [hf, ↓reduceIte]
        omega

theorem secondGapChordStart_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    B.secondGapChordStart j ≤ B.chord.length := by
  classical
  cases hnext : HalfGap.nextEntry B.brokenAssignment.index.second j with
  | none => simp [secondGapChordStart, hnext]
  | some e =>
      have hmem := HalfEntry.entrySource_mem
        B.brokenAssignment.index.second e
      have hlt := B.brokenAssignment.second.partner_lt
        (HalfEntry.entrySource B.brokenAssignment.index.second e) hmem
      simp only [secondGapChordStart, hnext]
      by_cases hf : B.secondGapRunsForward j
      · simp only [hf, ↓reduceIte]
        omega
      · simp only [hf, ↓reduceIte]
        omega

theorem secondGapChordFinish_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    B.secondGapChordFinish j ≤ B.chord.length := by
  classical
  cases hprev : HalfGap.previousEntry B.brokenAssignment.index.second j with
  | none => simp [secondGapChordFinish, hprev]
  | some e =>
      have hmem := HalfEntry.entrySource_mem
        B.brokenAssignment.index.second e
      have hlt := B.brokenAssignment.second.partner_lt
        (HalfEntry.entrySource B.brokenAssignment.index.second e) hmem
      simp only [secondGapChordFinish, hprev]
      by_cases hf : B.secondGapRunsForward j
      · simp only [hf, ↓reduceIte]
        omega
      · simp only [hf, ↓reduceIte]
        omega

/-- Local side coordinate occupied by a chord edge in a first-half gap. -/
noncomputable def firstGapChordTargetIndex
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) (y : ℕ) : ℕ :=
  auxiliaryChordTargetIndex (B.firstGapLeft j) (B.firstGapRight j)
    (B.firstGapFinishSide j - B.firstGapStartSide j)
    (B.firstGapChordStart j) (B.firstGapChordFinish j) y

/-- Local side coordinate occupied by a chord edge in a wrapped-half gap. -/
noncomputable def secondGapChordTargetIndex
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) (y : ℕ) : ℕ :=
  auxiliaryChordTargetIndex (B.secondGapLeft j) (B.secondGapRight j)
    (B.secondGapFinishSide j - B.secondGapStartSide j)
    (B.secondGapChordStart j) (B.secondGapChordFinish j) y

/-- A first-half broken partner has an actual local target coordinate in a
wrapped-half child, and that chord letter carries its source label. -/
theorem exists_secondGap_partnerCoordinate
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    ∃ j : Fin B.brokenAssignment.index.second.pieceCount,
      ∃ htarget : B.secondGapChordTargetIndex j
          (B.brokenAssignment.first.partner s) <
        (B.secondGapLeft j).length +
          (B.secondGapFinishSide j - B.secondGapStartSide j) +
          (B.secondGapRight j).length +
          (orientedSegment B.chord (B.secondGapChordStart j)
            (B.secondGapChordFinish j)).length,
      ((orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j))[
          orientedEdgeIndex (B.secondGapChordStart j)
            (B.secondGapChordFinish j)
            (B.brokenAssignment.first.partner s)]'(by
              unfold secondGapChordTargetIndex auxiliaryChordTargetIndex at htarget
              omega)).IsCompOf
        (P.label s) := by
  classical
  obtain ⟨j, hedge⟩ := B.exists_secondGap_containing_firstPartner s hs
  have htarget := auxiliaryChordTargetIndex_lt B.chord
      (B.secondGapLeft j) (B.secondGapRight j)
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (B.secondGapChordStart_le j) (B.secondGapChordFinish_le j) hedge
  refine ⟨j, htarget, ?_⟩
  exact orientedEdgeIndex_isCompOf B.chord (P.label s)
      (B.secondGapChordStart_le j) (B.secondGapChordFinish_le j)
      (B.brokenAssignment.first.partner_lt s hs) hedge
      (B.firstPartner_chordLetter_label s hs)

/-- A wrapped-half broken partner has an actual local target coordinate in a
first-half child, and that chord letter carries its source label. -/
theorem exists_firstGap_partnerCoordinate
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    ∃ j : Fin B.brokenAssignment.index.first.pieceCount,
      ∃ htarget : B.firstGapChordTargetIndex j
          (B.brokenAssignment.second.partner s) <
        (B.firstGapLeft j).length +
          (B.firstGapFinishSide j - B.firstGapStartSide j) +
          (B.firstGapRight j).length +
          (orientedSegment B.chord (B.firstGapChordStart j)
            (B.firstGapChordFinish j)).length,
      ((orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j))[
          orientedEdgeIndex (B.firstGapChordStart j)
            (B.firstGapChordFinish j)
            (B.brokenAssignment.second.partner s)]'(by
              unfold firstGapChordTargetIndex auxiliaryChordTargetIndex at htarget
              omega)).IsCompOf
        (P.label s) := by
  classical
  obtain ⟨j, hedge⟩ := B.exists_firstGap_containing_secondPartner s hs
  have htarget := auxiliaryChordTargetIndex_lt B.chord
      (B.firstGapLeft j) (B.firstGapRight j)
      (B.firstGapFinishSide j - B.firstGapStartSide j)
      (B.firstGapChordStart_le j) (B.firstGapChordFinish_le j) hedge
  refine ⟨j, htarget, ?_⟩
  exact orientedEdgeIndex_isCompOf B.chord (P.label s)
      (B.firstGapChordStart_le j) (B.firstGapChordFinish_le j)
      (B.brokenAssignment.second.partner_lt s hs) hedge
      (B.secondPartner_chordLetter_label s hs)

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
