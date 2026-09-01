import GroupApproximation.GGT.DGOProposition414GapIntervals

/-!
# Per-child side bounds for balanced component surgery

The two possible connectors at a gap replace the omitted boundary sides, so
the inherited arc together with its connectors never has more sides than its
whole balanced half.  Adding the oriented chord interval gives exactly the
per-child estimates required by `BalancedSplitIntervalSurgery`.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

theorem firstGapLeft_length_le_one
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    (B.firstGapLeft j).length ≤ 1 := by
  classical
  cases hprev : HalfGap.previousEntry B.brokenAssignment.index.first j with
  | none => simp [firstGapLeft, hprev]
  | some e =>
      let s := HalfEntry.entrySource B.brokenAssignment.index.first e
      have hs := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
      let C := B.firstBrokenConnectors s hs
      by_cases hforward : B.firstGapRunsForward j
      · simpa only [firstGapLeft, hprev, hforward, ↓reduceIte] using C.end_length
      · simpa only [firstGapLeft, hprev, hforward, ↓reduceIte] using
          C.endThroughPartner_length

theorem firstGapRight_length_le_one
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    (B.firstGapRight j).length ≤ 1 := by
  classical
  cases hnext : HalfGap.nextEntry B.brokenAssignment.index.first j with
  | none => simp [firstGapRight, hnext]
  | some e =>
      let s := HalfEntry.entrySource B.brokenAssignment.index.first e
      have hs := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
      let C := B.firstBrokenConnectors s hs
      by_cases hforward : B.firstGapRunsForward j
      · simpa only [firstGapRight, hnext, hforward, ↓reduceIte] using
          C.start_length
      · simpa only [firstGapRight, hnext, hforward, ↓reduceIte] using
          C.startThroughPartner_length

theorem secondGapLeft_length_le_one
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    (B.secondGapLeft j).length ≤ 1 := by
  classical
  cases hprev : HalfGap.previousEntry B.brokenAssignment.index.second j with
  | none => simp [secondGapLeft, hprev]
  | some e =>
      let s := HalfEntry.entrySource B.brokenAssignment.index.second e
      have hs := HalfEntry.entrySource_mem B.brokenAssignment.index.second e
      let C := B.secondBrokenConnectors s hs
      by_cases hforward : B.secondGapRunsForward j
      · simpa only [secondGapLeft, hprev, hforward, ↓reduceIte] using
          C.endThroughPartner_length
      · simpa only [secondGapLeft, hprev, hforward, ↓reduceIte] using C.end_length

theorem secondGapRight_length_le_one
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    (B.secondGapRight j).length ≤ 1 := by
  classical
  cases hnext : HalfGap.nextEntry B.brokenAssignment.index.second j with
  | none => simp [secondGapRight, hnext]
  | some e =>
      let s := HalfEntry.entrySource B.brokenAssignment.index.second e
      have hs := HalfEntry.entrySource_mem B.brokenAssignment.index.second e
      let C := B.secondBrokenConnectors s hs
      by_cases hforward : B.secondGapRunsForward j
      · simpa only [secondGapRight, hnext, hforward, ↓reduceIte] using
          C.startThroughPartner_length
      · simpa only [secondGapRight, hnext, hforward, ↓reduceIte] using
          C.start_length

theorem firstGapLeft_length_le_startSide
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    (B.firstGapLeft j).length ≤ B.firstGapStartSide j := by
  classical
  cases hprev : HalfGap.previousEntry B.brokenAssignment.index.first j with
  | none => simp [firstGapLeft, firstGapStartSide, hprev]
  | some e =>
      have hlen := B.firstGapLeft_length_le_one j
      have hstart : B.firstGapStartSide j =
          B.firstTargetSide
            (HalfEntry.entrySource B.brokenAssignment.index.first e) + 1 := by
        simp only [firstGapStartSide, hprev]
      omega

theorem secondGapLeft_length_le_startSide
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    (B.secondGapLeft j).length ≤ B.secondGapStartSide j := by
  classical
  cases hprev : HalfGap.previousEntry B.brokenAssignment.index.second j with
  | none => simp [secondGapLeft, secondGapStartSide, hprev]
  | some e =>
      have hlen := B.secondGapLeft_length_le_one j
      have hstart : B.secondGapStartSide j =
          B.secondTargetSide
            (HalfEntry.entrySource B.brokenAssignment.index.second e) + 1 := by
        simp only [secondGapStartSide, hprev]
      omega

theorem firstGapFinishSide_add_right_length_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    B.firstGapFinishSide j + (B.firstGapRight j).length ≤
      B.secondSide - B.firstSide + 1 := by
  classical
  cases hnext : HalfGap.nextEntry B.brokenAssignment.index.first j with
  | none => simp [firstGapFinishSide, firstGapRight, hnext]
  | some e =>
      let s := HalfEntry.entrySource B.brokenAssignment.index.first e
      have hs := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
      have htarget : s ∈ B.firstTarget := (mem_brokenSet_iff.mp hs).1
      have hside := B.firstTargetSide_lt htarget
      have hlen := B.firstGapRight_length_le_one j
      have hfinish : B.firstGapFinishSide j = B.firstTargetSide s := by
        simp only [firstGapFinishSide, hnext]
      omega

theorem secondGapFinishSide_add_right_length_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    B.secondGapFinishSide j + (B.secondGapRight j).length ≤
      (n - B.secondSide) + B.firstSide + 1 := by
  classical
  cases hnext : HalfGap.nextEntry B.brokenAssignment.index.second j with
  | none => simp [secondGapFinishSide, secondGapRight, hnext]
  | some e =>
      let s := HalfEntry.entrySource B.brokenAssignment.index.second e
      have hs := HalfEntry.entrySource_mem B.brokenAssignment.index.second e
      have htarget : s ∈ B.secondTarget := (mem_brokenSet_iff.mp hs).1
      have hside := B.secondTargetSide_lt htarget
      have hlen := B.secondGapRight_length_le_one j
      have hfinish : B.secondGapFinishSide j = B.secondTargetSide s := by
        simp only [secondGapFinishSide, hnext]
      omega

/-- A first-half child has at most the first-half side count plus one chord
length. -/
theorem firstGap_raw_side_bound
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    (B.firstGapLeft j).length +
        (B.firstGapFinishSide j - B.firstGapStartSide j) +
        (B.firstGapRight j).length +
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)).length ≤
      (B.secondSide - B.firstSide + 1) + B.chord.length := by
  have horder := B.firstGap_side_order j
  have hleft := B.firstGapLeft_length_le_startSide j
  have hright := B.firstGapFinishSide_add_right_length_le j
  have hsegment := length_orientedSegment B.chord
    (B.firstGapChordStart_le j) (B.firstGapChordFinish_le j)
  have hstart := B.firstGapChordStart_le j
  have hfinish := B.firstGapChordFinish_le j
  rw [hsegment]
  omega

/-- A wrapped-half child has at most the complementary-half side count plus
one chord length. -/
theorem secondGap_raw_side_bound
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    (B.secondGapLeft j).length +
        (B.secondGapFinishSide j - B.secondGapStartSide j) +
        (B.secondGapRight j).length +
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)).length ≤
      ((n - B.secondSide) + B.firstSide + 1) + B.chord.length := by
  have horder := B.secondGap_side_order j
  have hleft := B.secondGapLeft_length_le_startSide j
  have hright := B.secondGapFinishSide_add_right_length_le j
  have hsegment := length_orientedSegment B.chord
    (B.secondGapChordStart_le j) (B.secondGapChordFinish_le j)
  have hstart := B.secondGapChordStart_le j
  have hfinish := B.secondGapChordFinish_le j
  rw [hsegment]
  omega

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
