import GroupApproximation.GGT.DGOProposition414GapChordCounts
import GroupApproximation.GGT.DGOProposition414GapIntervalProducer

/-!
# Aggregate side-count bounds for balanced gap children

The inherited arcs telescope after adjoining the omitted broken sides.  The
four connector families are charged to the broken sources, and the two chord
families are charged to the two greedy partner traversals.  These estimates
give the global upper count required by balanced interval surgery, including
the degenerate zero-length chord case without an additive loss.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- The first family of oriented chord pieces is the first trimmed partner
walk, with no orientation loss when there are no partners. -/
theorem sum_firstGap_chord_length_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    (∑ j : Fin B.brokenAssignment.index.first.pieceCount,
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)).length) ≤
      chordTraversalCost
          (0 :: B.brokenAssignment.index.first.partners ++ [B.chord.length]) +
        4 * B.brokenAssignment.index.first.partners.length := by
  classical
  let A := B.brokenAssignment.index.first
  let e : Fin A.pieceCount ≃ Fin (A.partners.length + 1) :=
    finCongr (by simp [GreedyHalfFamilyIndex.pieceCount, A.partner_length])
  calc
    (∑ j : Fin A.pieceCount,
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)).length) =
      ∑ q : Fin (A.partners.length + 1),
        Nat.dist
          (if h : q.val < A.partners.length then
            endpointByOrientation (B.firstGapRunsForward (e.symm q))
              (A.partners[q.val] + 1) A.partners[q.val]
          else B.chord.length)
          (if h : 0 < q.val then
            endpointByOrientation (B.firstGapRunsForward (e.symm q))
              (A.partners[q.val - 1]'(by omega))
              (A.partners[q.val - 1]'(by omega) + 1)
          else 0) := by
            exact Fintype.sum_equiv e _ _ fun j => by
              rw [length_orientedSegment B.chord
                (B.firstGapChordStart_le j) (B.firstGapChordFinish_le j),
                B.firstGapChordStart_eq_trimmedWalk,
                B.firstGapChordFinish_eq_walk]
              simp [e, A]
    _ ≤ chordTraversalCost (0 :: A.partners ++ [B.chord.length]) +
          4 * A.partners.length :=
      sum_orientedTrimmedChordWalk_dist_le_four_length
        A.partners 0 B.chord.length
          (fun q => B.firstGapRunsForward (e.symm q))

/-- The wrapped family is the oppositely based trimmed partner walk. -/
theorem sum_secondGap_chord_length_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    (∑ j : Fin B.brokenAssignment.index.second.pieceCount,
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)).length) ≤
      chordTraversalCost
          (B.chord.length :: B.brokenAssignment.index.second.partners ++ [0]) +
        4 * B.brokenAssignment.index.second.partners.length := by
  classical
  let A := B.brokenAssignment.index.second
  let e : Fin A.pieceCount ≃ Fin (A.partners.length + 1) :=
    finCongr (by simp [GreedyHalfFamilyIndex.pieceCount, A.partner_length])
  calc
    (∑ j : Fin A.pieceCount,
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)).length) =
      ∑ q : Fin (A.partners.length + 1),
        Nat.dist
          (if h : q.val < A.partners.length then
            endpointByOrientation (B.secondGapRunsForward (e.symm q))
              (A.partners[q.val] + 1) A.partners[q.val]
          else 0)
          (if h : 0 < q.val then
            endpointByOrientation (B.secondGapRunsForward (e.symm q))
              (A.partners[q.val - 1]'(by omega))
              (A.partners[q.val - 1]'(by omega) + 1)
          else B.chord.length) := by
            exact Fintype.sum_equiv e _ _ fun j => by
              rw [length_orientedSegment B.chord
                (B.secondGapChordStart_le j) (B.secondGapChordFinish_le j),
                B.secondGapChordStart_eq_walk,
                B.secondGapChordFinish_eq_trimmedWalk]
              simp [e, A]
    _ ≤ chordTraversalCost (B.chord.length :: A.partners ++ [0]) +
          4 * A.partners.length :=
      sum_orientedTrimmedChordWalk_dist_le_four_length
        A.partners B.chord.length 0
          (fun q => B.secondGapRunsForward (e.symm q))

/-- Every noninitial first gap has at most one left connector, while the
initial gap has none. -/
theorem sum_firstGapLeft_length_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    (∑ j : Fin B.brokenAssignment.index.first.pieceCount,
      (B.firstGapLeft j).length) ≤
        B.brokenAssignment.index.first.sources.length := by
  classical
  change (∑ j : Fin
      (B.brokenAssignment.index.first.sources.length + 1),
        (B.firstGapLeft j).length) ≤
    B.brokenAssignment.index.first.sources.length
  rw [Fin.sum_univ_succ]
  have htail :
      (∑ j : Fin B.brokenAssignment.index.first.sources.length,
        (B.firstGapLeft j.succ).length) ≤
      ∑ _j : Fin B.brokenAssignment.index.first.sources.length, 1 := by
    apply Finset.sum_le_sum
    intro j _hj
    exact B.firstGapLeft_length_le_one j.succ
  simpa [GreedyHalfFamilyIndex.pieceCount, firstGapLeft,
    HalfGap.previousEntry] using htail

/-- Every nonfinal first gap has at most one right connector, while the final
gap has none. -/
theorem sum_firstGapRight_length_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    (∑ j : Fin B.brokenAssignment.index.first.pieceCount,
      (B.firstGapRight j).length) ≤
        B.brokenAssignment.index.first.sources.length := by
  classical
  change (∑ j : Fin
      (B.brokenAssignment.index.first.sources.length + 1),
        (B.firstGapRight j).length) ≤
    B.brokenAssignment.index.first.sources.length
  rw [Fin.sum_univ_castSucc]
  have hinit :
      (∑ j : Fin B.brokenAssignment.index.first.sources.length,
        (B.firstGapRight j.castSucc).length) ≤
      ∑ _j : Fin B.brokenAssignment.index.first.sources.length, 1 := by
    apply Finset.sum_le_sum
    intro j _hj
    exact B.firstGapRight_length_le_one j.castSucc
  have hlast :
      (B.firstGapRight
        (Fin.last B.brokenAssignment.index.first.sources.length)).length = 0 := by
    simp [GreedyHalfFamilyIndex.pieceCount, firstGapRight,
      HalfGap.nextEntry]
  rw [hlast, Nat.add_zero]
  simpa using hinit

/-- Wrapped left connectors have the same source-count bound. -/
theorem sum_secondGapLeft_length_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    (∑ j : Fin B.brokenAssignment.index.second.pieceCount,
      (B.secondGapLeft j).length) ≤
        B.brokenAssignment.index.second.sources.length := by
  classical
  change (∑ j : Fin
      (B.brokenAssignment.index.second.sources.length + 1),
        (B.secondGapLeft j).length) ≤
    B.brokenAssignment.index.second.sources.length
  rw [Fin.sum_univ_succ]
  have htail :
      (∑ j : Fin B.brokenAssignment.index.second.sources.length,
        (B.secondGapLeft j.succ).length) ≤
      ∑ _j : Fin B.brokenAssignment.index.second.sources.length, 1 := by
    apply Finset.sum_le_sum
    intro j _hj
    exact B.secondGapLeft_length_le_one j.succ
  simpa [GreedyHalfFamilyIndex.pieceCount, secondGapLeft,
    HalfGap.previousEntry] using htail

/-- Wrapped right connectors have the same source-count bound. -/
theorem sum_secondGapRight_length_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    (∑ j : Fin B.brokenAssignment.index.second.pieceCount,
      (B.secondGapRight j).length) ≤
        B.brokenAssignment.index.second.sources.length := by
  classical
  change (∑ j : Fin
      (B.brokenAssignment.index.second.sources.length + 1),
        (B.secondGapRight j).length) ≤
    B.brokenAssignment.index.second.sources.length
  rw [Fin.sum_univ_castSucc]
  have hinit :
      (∑ j : Fin B.brokenAssignment.index.second.sources.length,
        (B.secondGapRight j.castSucc).length) ≤
      ∑ _j : Fin B.brokenAssignment.index.second.sources.length, 1 := by
    apply Finset.sum_le_sum
    intro j _hj
    exact B.secondGapRight_length_le_one j.castSucc
  have hlast :
      (B.secondGapRight
        (Fin.last B.brokenAssignment.index.second.sources.length)).length = 0 := by
    simp [GreedyHalfFamilyIndex.pieceCount, secondGapRight,
      HalfGap.nextEntry]
  rw [hlast, Nat.add_zero]
  simpa using hinit

/-- Both trimmed chord families together cost at most the two quadratic
traversals plus their endpoint and orientation corrections. -/
theorem sum_gapChord_length_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    (∑ j : Fin B.brokenAssignment.index.first.pieceCount,
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)).length) +
      (∑ j : Fin B.brokenAssignment.index.second.pieceCount,
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)).length) ≤
      2 * (B.chord.length * B.chord.length) + 12 * B.chord.length := by
  let A₁ := B.brokenAssignment.index.first
  let A₂ := B.brokenAssignment.index.second
  have h₁ := B.sum_firstGap_chord_length_le
  have h₂ := B.sum_secondGap_chord_length_le
  have ht₁ := chordTraversalCost_with_two_endpoints_le
    (xs := A₁.partners) (initial := 0) (terminal := B.chord.length)
    (L := B.chord.length) (Nat.zero_le _) (le_refl _)
    (fun x hx => le_of_lt (A₁.partner_lt x hx))
  have ht₂ := chordTraversalCost_with_two_endpoints_le
    (xs := A₂.partners) (initial := B.chord.length) (terminal := 0)
    (L := B.chord.length) (le_refl _) (Nat.zero_le _)
    (fun x hx => le_of_lt (A₂.partner_lt x hx))
  have hi₁ := A₁.traversal
  have hi₂ := A₂.traversal
  have hm₁ : A₁.partners.length ≤ B.chord.length := by
    rw [A₁.partner_length, A₁.source_length]
    exact A₁.source_count_le
  have hm₂ : A₂.partners.length ≤ B.chord.length := by
    rw [A₂.partner_length, A₂.source_length]
    exact A₂.source_count_le
  dsimp only [A₁, A₂] at ht₁ ht₂ hi₁ hi₂ hm₁ hm₂
  unfold ChordPartnerQuadraticTraversalBound at hi₁ hi₂
  omega

/-- All four connector families together cost at most four chord lengths. -/
theorem sum_gapConnector_length_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    ((∑ j : Fin B.brokenAssignment.index.first.pieceCount,
        (B.firstGapLeft j).length) +
      ∑ j : Fin B.brokenAssignment.index.first.pieceCount,
        (B.firstGapRight j).length) +
      ((∑ j : Fin B.brokenAssignment.index.second.pieceCount,
        (B.secondGapLeft j).length) +
      ∑ j : Fin B.brokenAssignment.index.second.pieceCount,
        (B.secondGapRight j).length) ≤ 4 * B.chord.length := by
  have hfl := B.sum_firstGapLeft_length_le
  have hfr := B.sum_firstGapRight_length_le
  have hsl := B.sum_secondGapLeft_length_le
  have hsr := B.sum_secondGapRight_length_le
  have hm₁ := B.brokenAssignment.index.first.source_count_le
  have hm₂ := B.brokenAssignment.index.second.source_count_le
  rw [← B.brokenAssignment.index.first.source_length] at hm₁
  rw [← B.brokenAssignment.index.second.source_length] at hm₂
  omega

/-- The two balanced half lengths add to the original polygon length plus the
two new cut endpoints. -/
theorem balancedHalfLengths_add
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    (B.secondSide - B.firstSide + 1) +
      ((n - B.secondSide) + B.firstSide + 1) = n + 2 := by
  have h₁ := B.side_order
  have h₂ := B.secondSide_lt
  omega

/-- Raw canonical gap children satisfy the global quadratic upper count. -/
theorem sum_rawGap_sideCount_upper
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
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
          (B.secondGapChordFinish j)).length)) ≤
      n + 6 * ((2 * B.chord.length + 1) *
        (2 * B.chord.length + 1)) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  have ha₁ := B.sum_firstGap_arcSides_add_broken
  have ha₂ := B.sum_secondGap_arcSides_add_broken
  have hh := B.balancedHalfLengths_add
  have hc := B.sum_gapConnector_length_le
  have hd := B.sum_gapChord_length_le
  nlinarith

/-- The canonical interval family therefore supplies the upper-count field of
`BalancedSplitGapCompletion`, independently of its component files. -/
theorem gapIntervalsOfConfigurations_count_upper
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B) :
    (∑ j, (((B.gapIntervalsOfConfigurations C).toPathInput).first j).sideCount) +
        ∑ j, (((B.gapIntervalsOfConfigurations C).toPathInput).second j).sideCount ≤
      n + 6 * ((2 * B.chord.length + 1) *
        (2 * B.chord.length + 1)) := by
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
  exact B.sum_rawGap_sideCount_upper

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
