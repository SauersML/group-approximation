import GroupApproximation.GGT.DGOProposition414GapAggregateBounds

/-!
# Lower side count for balanced gap children

Every broken distinguished component has an injectively chosen partner edge
on the global chord.  The opposite-half occurrence theorem places that edge
in a canonical child chord interval.  Counting the union of these edge
intervals pays for all omitted broken sides, so the total child side count is
at least the original polygon side count.  This is the lower-count step in
Dahmani--Guirardel--Osin Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The finite set of chord edges crossed by the unoriented interval with
endpoints `a,b`. -/
def chordEdgeInterval (a b : ℕ) : Finset ℕ :=
  Finset.Ico (min a b) (max a b)

omit [Group G] in
/-- Membership in the finite chord-edge interval is exactly `EdgeBetween`. -/
theorem mem_chordEdgeInterval_iff {a b y : ℕ} :
    y ∈ chordEdgeInterval a b ↔ EdgeBetween a b y := by
  by_cases hab : a ≤ b
  · simp [chordEdgeInterval, EdgeBetween, min_eq_left hab, max_eq_right hab]
    omega
  · have hba : b ≤ a := le_of_not_ge hab
    simp [chordEdgeInterval, EdgeBetween, min_eq_right hba, max_eq_left hba]
    omega

omit [Group G] in
/-- The number of crossed chord edges is the distance between the endpoints. -/
theorem card_chordEdgeInterval (a b : ℕ) :
    (chordEdgeInterval a b).card = Nat.dist a b := by
  by_cases hab : a ≤ b
  · simp [chordEdgeInterval, min_eq_left hab, max_eq_right hab,
      Nat.dist_eq_sub_of_le hab]
  · have hba : b ≤ a := le_of_not_ge hab
    simp [chordEdgeInterval, min_eq_right hba, max_eq_left hba,
      Nat.dist_comm, Nat.dist_eq_sub_of_le hba]

namespace BalancedSplitData

/-- The wrapped child chord intervals contain at least one distinct edge for
every broken first-half component. -/
theorem firstBroken_card_le_sum_secondGapChord_length
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    (brokenSet B.componentPlacement.firstTarget
        B.componentPlacement.firstSurvives).card ≤
      ∑ j : Fin B.brokenAssignment.index.second.pieceCount,
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)).length := by
  classical
  let I := brokenSet B.componentPlacement.firstTarget
    B.componentPlacement.firstSurvives
  let partner := B.brokenAssignment.first.partner
  let cover := (Finset.univ :
      Finset (Fin B.brokenAssignment.index.second.pieceCount)).biUnion fun j =>
    chordEdgeInterval (B.secondGapChordStart j) (B.secondGapChordFinish j)
  have himage : (I.image partner).card = I.card := by
    exact Finset.card_image_iff.mpr fun s hs t ht heq =>
      B.brokenAssignment.first.partner_injective
        (by simpa only [I] using hs) (by simpa only [I] using ht) heq
  have hsubset : I.image partner ⊆ cover := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨j, hj⟩ := B.exists_secondGap_containing_firstPartner s
      (by simpa only [I] using hs)
    apply Finset.mem_biUnion.mpr
    exact ⟨j, Finset.mem_univ j, mem_chordEdgeInterval_iff.mpr hj⟩
  calc
    I.card = (I.image partner).card := himage.symm
    _ ≤ cover.card := Finset.card_le_card hsubset
    _ ≤ ∑ j : Fin B.brokenAssignment.index.second.pieceCount,
          (chordEdgeInterval (B.secondGapChordStart j)
            (B.secondGapChordFinish j)).card := by
        simpa only [cover]
          using (Finset.card_biUnion_le :
            cover.card ≤ ∑ j ∈ (Finset.univ :
              Finset (Fin B.brokenAssignment.index.second.pieceCount)),
                (chordEdgeInterval (B.secondGapChordStart j)
                  (B.secondGapChordFinish j)).card)
    _ = ∑ j : Fin B.brokenAssignment.index.second.pieceCount,
          (orientedSegment B.chord (B.secondGapChordStart j)
            (B.secondGapChordFinish j)).length := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [card_chordEdgeInterval,
          length_orientedSegment B.chord
            (B.secondGapChordStart_le j) (B.secondGapChordFinish_le j)]

/-- The first child chord intervals contain at least one distinct edge for
every broken wrapped-half component. -/
theorem secondBroken_card_le_sum_firstGapChord_length
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    (brokenSet B.componentPlacement.secondTarget
        B.componentPlacement.secondSurvives).card ≤
      ∑ j : Fin B.brokenAssignment.index.first.pieceCount,
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)).length := by
  classical
  let I := brokenSet B.componentPlacement.secondTarget
    B.componentPlacement.secondSurvives
  let partner := B.brokenAssignment.second.partner
  let cover := (Finset.univ :
      Finset (Fin B.brokenAssignment.index.first.pieceCount)).biUnion fun j =>
    chordEdgeInterval (B.firstGapChordStart j) (B.firstGapChordFinish j)
  have himage : (I.image partner).card = I.card := by
    exact Finset.card_image_iff.mpr fun s hs t ht heq =>
      B.brokenAssignment.second.partner_injective
        (by simpa only [I] using hs) (by simpa only [I] using ht) heq
  have hsubset : I.image partner ⊆ cover := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨j, hj⟩ := B.exists_firstGap_containing_secondPartner s
      (by simpa only [I] using hs)
    apply Finset.mem_biUnion.mpr
    exact ⟨j, Finset.mem_univ j, mem_chordEdgeInterval_iff.mpr hj⟩
  calc
    I.card = (I.image partner).card := himage.symm
    _ ≤ cover.card := Finset.card_le_card hsubset
    _ ≤ ∑ j : Fin B.brokenAssignment.index.first.pieceCount,
          (chordEdgeInterval (B.firstGapChordStart j)
            (B.firstGapChordFinish j)).card := by
        simpa only [cover]
          using (Finset.card_biUnion_le :
            cover.card ≤ ∑ j ∈ (Finset.univ :
              Finset (Fin B.brokenAssignment.index.first.pieceCount)),
                (chordEdgeInterval (B.firstGapChordStart j)
                  (B.firstGapChordFinish j)).card)
    _ = ∑ j : Fin B.brokenAssignment.index.first.pieceCount,
          (orientedSegment B.chord (B.firstGapChordStart j)
            (B.firstGapChordFinish j)).length := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [card_chordEdgeInterval,
          length_orientedSegment B.chord
            (B.firstGapChordStart_le j) (B.firstGapChordFinish_le j)]

/-- The raw canonical gap children have total side count at least `n`. -/
theorem sum_rawGap_sideCount_lower
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    n ≤
      (∑ j : Fin B.brokenAssignment.index.first.pieceCount,
        ((B.firstGapLeft j).length +
          (B.firstGapFinishSide j - B.firstGapStartSide j) +
          (B.firstGapRight j).length +
          (orientedSegment B.chord (B.firstGapChordStart j)
            (B.firstGapChordFinish j)).length)) +
      (∑ j : Fin B.brokenAssignment.index.second.pieceCount,
        ((B.secondGapLeft j).length +
          (B.secondGapFinishSide j - B.secondGapStartSide j) +
          (B.secondGapRight j).length +
          (orientedSegment B.chord (B.secondGapChordStart j)
            (B.secondGapChordFinish j)).length)) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  have ha₁ := B.sum_firstGap_arcSides_add_broken
  have ha₂ := B.sum_secondGap_arcSides_add_broken
  have hh := B.balancedHalfLengths_add
  have hc₁ := B.secondBroken_card_le_sum_firstGapChord_length
  have hc₂ := B.firstBroken_card_le_sum_secondGapChord_length
  omega

/-- The canonical interval family supplies the lower-count field of
`BalancedSplitGapCompletion`. -/
theorem gapIntervalsOfConfigurations_count_lower
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B) :
    n ≤
      (∑ j, (((B.gapIntervalsOfConfigurations C).toPathInput).first j).sideCount) +
        ∑ j, (((B.gapIntervalsOfConfigurations C).toPathInput).second j).sideCount := by
  have hfirst :
      (∑ j, (((B.gapIntervalsOfConfigurations C).toPathInput).first j).sideCount) =
        ∑ j : Fin B.brokenAssignment.index.first.pieceCount,
          ((B.firstGapLeft j).length +
            (B.firstGapFinishSide j - B.firstGapStartSide j) +
            (B.firstGapRight j).length +
            (orientedSegment B.chord (B.firstGapChordStart j)
              (B.firstGapChordFinish j)).length) := by
    apply Finset.sum_congr rfl
    intro j _hj
    let S := (B.gapIntervalsOfConfigurations C).first j
    have hshape := B.gapIntervalsOfConfigurations_first_shape C j
    change S.toPathInput.sideCount = _
    rw [S.toPathInput_sideCount, hshape.1, hshape.2.1, hshape.2.2.1,
      hshape.2.2.2.1, hshape.2.2.2.2]
  have hsecond :
      (∑ j, (((B.gapIntervalsOfConfigurations C).toPathInput).second j).sideCount) =
        ∑ j : Fin B.brokenAssignment.index.second.pieceCount,
          ((B.secondGapLeft j).length +
            (B.secondGapFinishSide j - B.secondGapStartSide j) +
            (B.secondGapRight j).length +
            (orientedSegment B.chord (B.secondGapChordStart j)
              (B.secondGapChordFinish j)).length) := by
    apply Finset.sum_congr rfl
    intro j _hj
    let S := (B.gapIntervalsOfConfigurations C).second j
    have hshape := B.gapIntervalsOfConfigurations_second_shape C j
    change S.toPathInput.sideCount = _
    rw [S.toPathInput_sideCount, hshape.1, hshape.2.1, hshape.2.2.1,
      hshape.2.2.2.1, hshape.2.2.2.2]
  rw [hfirst, hsecond]
  exact B.sum_rawGap_sideCount_lower

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
