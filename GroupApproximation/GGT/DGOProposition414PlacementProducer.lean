import GroupApproximation.GGT.DGOProposition414BalancedPlacement
import GroupApproximation.GGT.DGOAssemblyIsolation

/-!
# Producing balanced-half component placement from arc data

The raw split geometry identifies each original distinguished component with
one of the two half arcs.  This file turns those identifications into the
strong placement object used by the greedy broken-component assignment.
Separation along each arc and existence of every broken chord partner are
derived from the original isolation hypotheses, rather than repeated as raw
inputs.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The direct output of transporting original target components to the two
arcs of a balanced split.  The second arc is expressed in the rotated original
word, which is the coordinate system used by `secondHalf`. -/
structure BalancedSplitArcPlacement
    (D : RelGenSet G Λ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {n : ℕ} (P : SumBoundInput D (b : ℝ) n) {k R : ℕ}
    (B : BalancedSplitData D hsymm b hδ P k R) where
  firstTarget : Finset ℕ
  secondTarget : Finset ℕ
  target_disjoint : Disjoint firstTarget secondTarget
  target_cover : P.target = firstTarget ∪ secondTarget
  firstPos : ℕ → ℕ
  secondPos : ℕ → ℕ
  firstPos_injective : Set.InjOn firstPos (↑firstTarget : Set ℕ)
  secondPos_injective : Set.InjOn secondPos (↑secondTarget : Set ℕ)
  first_pos_lt : ∀ s ∈ firstTarget, firstPos s < B.firstArcLength
  second_pos_lt : ∀ s ∈ secondTarget, secondPos s < B.secondArcLength
  first_start : ∀ s ∈ firstTarget,
    IsCompStart (P.label s) B.firstWord (firstPos s)
  second_start : ∀ s ∈ secondTarget,
    IsCompStart (P.label s) B.secondWord (secondPos s)
  first_original_component : ∀ s ∈ firstTarget,
    IsComp (P.label s) P.word
      (B.firstVertex + firstPos s) (B.firstVertex + firstPos s + 1)
  first_original_isolated : ∀ s ∈ firstTarget,
    IsIsolated D.fam (P.label s) P.basepoint P.word
      (B.firstVertex + firstPos s)
  second_rotated_component : ∀ s ∈ secondTarget,
    IsComp (P.label s) (rotWord P.word B.secondVertex)
      (secondPos s) (secondPos s + 1)
  second_rotated_isolated : ∀ s ∈ secondTarget,
    IsIsolated D.fam (P.label s) B.secondBase
      (rotWord P.word B.secondVertex) (secondPos s)

namespace BalancedSplitArcPlacement

private theorem first_endpoint_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R} :
    B.refinedCut (B.secondSide + 2) ≤ P.word.length := by
  rw [BalancedSplitData.refinedCut, splitPairCut_right]
  exact B.secondVertex_mem.2.trans
    (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))

private theorem split_vertices_ordered
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R} :
    B.refinedCut (B.firstSide + 1) ≤
      B.refinedCut (B.secondSide + 2) := by
  rw [BalancedSplitData.refinedCut, splitPairCut_left B.side_order,
    splitPairCut_right]
  exact B.firstVertex_mem.2.trans
    ((P.polygonCut.mono_le (Nat.succ_le_iff.mpr B.side_order)).trans
      B.secondVertex_mem.1)

/-- Arc placement produces the exact split-component placement.  In
particular, every failure of isolation receives a local chord coordinate with
the correct reversal on the first half and forward orientation on the second. -/
noncomputable def componentPlacement
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (Q : BalancedSplitArcPlacement D hsymm b hδ P B) :
    BalancedSplitComponentPlacement D hsymm b hδ P B := by
  let firstSurvives : ℕ → Prop := fun s =>
    IsIsolated D.fam (P.label s) B.firstBase B.firstWord (Q.firstPos s)
  let secondSurvives : ℕ → Prop := fun s =>
    IsIsolated D.fam (P.label s) B.secondBase B.secondWord (Q.secondPos s)
  refine
    { firstTarget := Q.firstTarget
      secondTarget := Q.secondTarget
      target_disjoint := Q.target_disjoint
      target_cover := Q.target_cover
      firstPos := Q.firstPos
      secondPos := Q.secondPos
      firstPos_injective := Q.firstPos_injective
      secondPos_injective := Q.secondPos_injective
      first_start := Q.first_start
      second_start := Q.second_start
      first_separated := ?_
      second_separated := ?_
      first_partner := ?_
      second_partner := ?_ }
  · intro s hs t ht hlabel hne
    have hsTarget := (mem_brokenSet_iff.mp hs).1
    have htTarget := (mem_brokenSet_iff.mp ht).1
    have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
      simp [BalancedSplitData.refinedCut, splitPairCut_left B.side_order]
    have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
      simp [BalancedSplitData.refinedCut, splitPairCut_right]
    change ¬ Connected D.fam (P.label s)
      (vertex P.basepoint P.word B.firstVertex)
      (firstHalf P.word B.refinedCut (B.firstSide + 1)
        (B.secondSide + 2) B.chord) (Q.firstPos s) (Q.firstPos t)
    rw [← hleft]
    apply not_connected_firstHalf_arc D (P.label s) P.basepoint P.word
      B.refinedCut (a := B.firstSide + 1) (b := B.secondSide + 2)
      (i := Q.firstPos s) (j := Q.firstPos t) P.letters first_endpoint_le
      (by simpa only [hleft, hright, BalancedSplitData.firstArcLength] using
        Q.first_pos_lt s hsTarget)
      (by simpa only [hleft, hright, BalancedSplitData.firstArcLength] using
        Q.first_pos_lt t htTarget)
      hne.symm
    · simpa [BalancedSplitData.refinedCut,
        splitPairCut_left B.side_order] using
        Q.first_original_component s hsTarget
    · simpa [BalancedSplitData.refinedCut,
        splitPairCut_left B.side_order] using
        Q.first_original_isolated s hsTarget
    · simpa [BalancedSplitData.firstWord, hlabel] using Q.first_start t htTarget
  · intro s hs t ht hlabel hne
    have hsTarget := (mem_brokenSet_iff.mp hs).1
    have htTarget := (mem_brokenSet_iff.mp ht).1
    have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
      simp [BalancedSplitData.refinedCut, splitPairCut_left B.side_order]
    have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
      simp [BalancedSplitData.refinedCut, splitPairCut_right]
    change ¬ Connected D.fam (P.label s)
      (vertex P.basepoint P.word B.secondVertex)
      (secondHalf P.word B.refinedCut (B.firstSide + 1)
        (B.secondSide + 2) B.chord) (Q.secondPos s) (Q.secondPos t)
    rw [← hright]
    apply not_connected_secondHalf_arc D (P.label s) P.basepoint P.word
      B.refinedCut (a := B.firstSide + 1) (b := B.secondSide + 2)
      (i := Q.secondPos s) (j := Q.secondPos t) P.letters
      split_vertices_ordered first_endpoint_le
      (by simpa only [hleft, hright, BalancedSplitData.secondArcLength] using
        Q.second_pos_lt s hsTarget)
      (by simpa only [hleft, hright, BalancedSplitData.secondArcLength] using
        Q.second_pos_lt t htTarget)
      hne.symm
    · simpa [BalancedSplitData.refinedCut, splitPairCut_right,
        BalancedSplitData.secondBase] using Q.second_rotated_component s hsTarget
    · simpa [BalancedSplitData.refinedCut, splitPairCut_right,
        BalancedSplitData.secondBase] using Q.second_rotated_isolated s hsTarget
    · simpa [BalancedSplitData.secondWord, hlabel] using Q.second_start t htTarget
  · intro s hs
    have hsTarget := (mem_brokenSet_iff.mp hs).1
    have hsNot := (mem_brokenSet_iff.mp hs).2
    have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
      simp [BalancedSplitData.refinedCut, splitPairCut_left B.side_order]
    have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
      simp [BalancedSplitData.refinedCut, splitPairCut_right]
    change ¬ IsIsolated D.fam (P.label s)
      (vertex P.basepoint P.word B.firstVertex)
      (firstHalf P.word B.refinedCut (B.firstSide + 1)
        (B.secondSide + 2) B.chord) (Q.firstPos s) at hsNot
    rw [← hleft] at hsNot
    obtain ⟨j, hjArc, hjStart, hjConn⟩ :=
      exists_chord_partner_firstHalf D (P.label s) P.basepoint P.word
        B.refinedCut (a := B.firstSide + 1) (b := B.secondSide + 2)
        (i := Q.firstPos s) P.letters first_endpoint_le
        (by simpa only [hleft, hright, BalancedSplitData.firstArcLength] using
          Q.first_pos_lt s hsTarget)
        (by simpa [BalancedSplitData.refinedCut,
            splitPairCut_left B.side_order] using
          Q.first_original_component s hsTarget)
        (by simpa [BalancedSplitData.refinedCut,
            splitPairCut_left B.side_order] using
          Q.first_original_isolated s hsTarget)
        B.chord (by simpa [BalancedSplitData.firstWord] using
          Q.first_start s hsTarget)
        hsNot
    have hjlen : j < B.firstWord.length := by
      obtain ⟨_jEnd, hjComp⟩ := hjStart
      exact lt_of_lt_of_le hjComp.1 hjComp.2.1
    have hwordLength : B.firstWord.length =
        B.firstArcLength + B.chord.length := by
      rw [BalancedSplitData.firstWord, length_firstHalf P.word B.refinedCut
        first_endpoint_le]
      rw [hleft, hright]
      rfl
    rw [hwordLength] at hjlen
    have hjArc' : B.firstArcLength ≤ j := by
      simpa only [hleft, hright, BalancedSplitData.firstArcLength] using hjArc
    let q := j - B.firstArcLength
    have hq : q < B.chord.length := by
      dsimp [q]
      omega
    let y := B.chord.length - 1 - q
    have hy : y < B.chord.length := by
      dsimp [y]
      omega
    have hpos : B.firstChordPos y = j := by
      simp only [BalancedSplitData.firstChordPos]
      dsimp [y, q]
      omega
    exact ⟨y, hy,
      by simpa only [hpos, BalancedSplitData.firstWord] using hjStart,
      by simpa only [hpos, BalancedSplitData.firstBase,
        BalancedSplitData.firstWord, hleft] using hjConn⟩
  · intro s hs
    have hsTarget := (mem_brokenSet_iff.mp hs).1
    have hsNot := (mem_brokenSet_iff.mp hs).2
    have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
      simp [BalancedSplitData.refinedCut, splitPairCut_left B.side_order]
    have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
      simp [BalancedSplitData.refinedCut, splitPairCut_right]
    change ¬ IsIsolated D.fam (P.label s)
      (vertex P.basepoint P.word B.secondVertex)
      (secondHalf P.word B.refinedCut (B.firstSide + 1)
        (B.secondSide + 2) B.chord) (Q.secondPos s) at hsNot
    rw [← hright] at hsNot
    obtain ⟨j, hjArc, hjStart, hjConn⟩ :=
      exists_chord_partner_secondHalf D (P.label s) P.basepoint P.word
        B.refinedCut (a := B.firstSide + 1) (b := B.secondSide + 2)
        (i := Q.secondPos s) P.letters split_vertices_ordered first_endpoint_le
        (by simpa only [hleft, hright, BalancedSplitData.secondArcLength] using
          Q.second_pos_lt s hsTarget)
        (by simpa [BalancedSplitData.refinedCut, splitPairCut_right,
            BalancedSplitData.secondBase] using
          Q.second_rotated_component s hsTarget)
        (by simpa [BalancedSplitData.refinedCut, splitPairCut_right,
            BalancedSplitData.secondBase] using
          Q.second_rotated_isolated s hsTarget)
        B.chord (by simpa [BalancedSplitData.secondWord] using
          Q.second_start s hsTarget)
        hsNot
    have hjlen : j < B.secondWord.length := by
      obtain ⟨_jEnd, hjComp⟩ := hjStart
      simpa [BalancedSplitData.secondWord] using
        (lt_of_lt_of_le hjComp.1 hjComp.2.1)
    have hwordLength : B.secondWord.length =
        B.secondArcLength + B.chord.length := by
      rw [BalancedSplitData.secondWord, length_secondHalf P.word B.refinedCut]
      · rw [hleft, hright]
        rfl
      · rw [BalancedSplitData.refinedCut, splitPairCut_left B.side_order]
        exact B.firstVertex_mem.2.trans
          (P.polygonCut.le_length
            ((Nat.succ_le_iff.mpr B.side_order).trans
              (le_of_lt B.secondSide_lt)))
    rw [hwordLength] at hjlen
    have hjArc' : B.secondArcLength ≤ j := by
      simpa only [hleft, hright, BalancedSplitData.secondArcLength] using hjArc
    let y := j - B.secondArcLength
    have hy : y < B.chord.length := by
      dsimp [y]
      omega
    have hpos : B.secondChordPos y = j := by
      simp only [BalancedSplitData.secondChordPos]
      dsimp [y]
      omega
    exact ⟨y, hy,
      by simpa only [hpos, BalancedSplitData.secondWord] using hjStart,
      by simpa only [hpos, BalancedSplitData.secondBase,
        BalancedSplitData.secondWord, hright] using hjConn⟩

end BalancedSplitArcPlacement

end DGOProposition414
end GGT
end GroupApproximation
