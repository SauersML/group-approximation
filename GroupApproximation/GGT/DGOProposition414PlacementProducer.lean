import GroupApproximation.GGT.DGOProposition414BalancedPlacement
import GroupApproximation.GGT.DGOAssemblyIsolation
import GroupApproximation.GGT.DGOComponentRestriction

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

/-- If appending a path destroys the exact one-edge maximality of a source
which was maximal in the open arc, the source lies at the seam and the first
appended letter is a same-label partner connected to it.  This is the seam
case missed by a partner interface phrased only in terms of component starts
of the concatenated word. -/
theorem exists_appendSeamPartner_of_not_exact
    (D : RelGenSet G Λ) (lam : Λ) (base : G)
    (arc tail : List (RelLetter G Λ)) (pos : ℕ)
    (letters : ∀ x ∈ arc ++ tail, D.IsLetter x)
    (hpos : pos < arc.length)
    (harc : IsComp lam arc pos (pos + 1))
    (hstart : IsCompStart lam (arc ++ tail) pos)
    (hnot : ¬ IsComp lam (arc ++ tail) pos (pos + 1)) :
    ∃ hseam : arc.length < (arc ++ tail).length,
      ((arc ++ tail)[arc.length]'hseam).IsCompOf lam ∧
      Connected D.fam lam base (arc ++ tail) pos arc.length := by
  obtain ⟨finish, hfull⟩ := hstart
  have hfinish : pos + 1 < finish := by
    have hpfinish := hfull.1
    by_contra hle
    have heq : finish = pos + 1 := by omega
    subst finish
    exact hnot hfull
  have hseamEq : pos + 1 = arc.length := by
    by_contra hne
    have hinside : pos + 1 < arc.length := by omega
    have hhalfLen : pos + 1 < (arc ++ tail).length := by simp; omega
    have hhalfLetter :
        ((arc ++ tail)[pos + 1]'hhalfLen).IsCompOf lam :=
      hfull.2.2.1 (pos + 1) (by omega) (by omega) hhalfLen
    have harcLetter : (arc[pos + 1]'hinside).IsCompOf lam := by
      rw [← List.getElem_append_left hinside]
      exact hhalfLetter
    exact harc.2.2.2.2 hinside harcLetter
  have hseam : arc.length < (arc ++ tail).length := by
    rw [← hseamEq]
    exact hfinish.trans_le hfull.2.1
  refine ⟨hseam, ?_, ?_⟩
  · exact hfull.2.2.1 arc.length (by omega) (by omega) hseam
  · show (vertex base (arc ++ tail) pos)⁻¹ *
        vertex base (arc ++ tail) arc.length ∈ D.fam lam
    rw [← hseamEq, vertex_succ (arc ++ tail) base pos (by omega)]
    simpa only [inv_mul_cancel_left] using
      val_mem_fam_of_isCompOf D
        (letters _ (List.getElem_mem (show pos < (arc ++ tail).length by omega)))
        (hfull.2.2.1 pos le_rfl hfull.1 (by omega))

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
    survivesExactly D P.label B.firstBase B.firstWord Q.firstPos s
  let secondSurvives : ℕ → Prop := fun s =>
    survivesExactly D P.label B.secondBase B.secondWord Q.secondPos s
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
    change ¬ survivesExactly D P.label B.firstBase B.firstWord Q.firstPos s
      at hsNot
    by_cases hExact : IsComp (P.label s) B.firstWord
        (Q.firstPos s) (Q.firstPos s + 1)
    · have hsNotIso : ¬ IsIsolated D.fam (P.label s)
          (vertex P.basepoint P.word B.firstVertex)
          (firstHalf P.word B.refinedCut (B.firstSide + 1)
            (B.secondSide + 2) B.chord) (Q.firstPos s) := by
        intro hiso
        exact hsNot ⟨hExact, by
          simpa [BalancedSplitData.firstBase, BalancedSplitData.firstWord] using
            hiso⟩
      rw [← hleft] at hsNotIso
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
          hsNotIso
      have hjlen : j < B.firstWord.length := by
        obtain ⟨_jEnd, hjComp⟩ := hjStart
        exact lt_of_lt_of_le hjComp.1 hjComp.2.1
      have hwordLength : B.firstWord.length =
          B.firstArcLength + B.chord.length := by
        rw [BalancedSplitData.firstWord, length_firstHalf P.word B.refinedCut
          first_endpoint_le]
        rw [hleft, hright]
        rfl
      have hjWordLen := hjlen
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
      have hjLetter : (B.firstWord[j]'hjWordLen).IsCompOf (P.label s) := by
        obtain ⟨jEnd, hjComp⟩ := hjStart
        exact hjComp.2.2.1 j le_rfl hjComp.1 hjWordLen
      refine ⟨y, hy, ?_, ?_, ?_⟩
      · simpa only [hpos] using hjWordLen
      · simpa only [hpos] using hjLetter
      · simpa only [hpos, BalancedSplitData.firstBase,
          BalancedSplitData.firstWord, hleft] using hjConn
    · let arc := arcWord P.word B.refinedCut (B.firstSide + 1)
          (B.secondSide + 2)
      have hArcLen : arc.length = B.firstArcLength := by
        dsimp [arc]
        rw [length_arcWord P.word B.refinedCut first_endpoint_le,
          hleft, hright]
        rfl
      have hsource : IsComp (P.label s) arc
          (Q.firstPos s) (Q.firstPos s + 1) := by
        have hcomp := Q.first_original_component s hsTarget
        have hvorder : B.firstVertex ≤ B.secondVertex := by
          rw [← hleft, ← hright]
          exact split_vertices_ordered
        have hsecondLe : B.secondVertex ≤ P.word.length := by
          rw [← hright]
          exact first_endpoint_le
        have hseg := isComp_segment_of_isComp (P.label s) P.word
          (start := B.firstVertex) (len := B.secondVertex - B.firstVertex)
          (i := Q.firstPos s) (finish := Q.firstPos s + 1)
          (by simpa [Nat.add_assoc] using hcomp)
          (by rw [Nat.add_sub_of_le hvorder]; exact hsecondLe)
          (by simpa only [BalancedSplitData.firstArcLength] using
            Nat.succ_le_iff.mpr (Q.first_pos_lt s hsTarget))
        dsimp [arc, arcWord]
        rw [hleft, hright]
        exact hseg
      have hletters : ∀ x ∈ arc ++ revWord B.chord, D.IsLetter x := by
        change ∀ x ∈ firstHalf P.word B.refinedCut (B.firstSide + 1)
          (B.secondSide + 2) B.chord, D.IsLetter x
        exact isLetter_firstHalf D hsymm P.letters
          B.chord_geodesic.1 B.refinedCut (B.firstSide + 1)
            (B.secondSide + 2)
      have hstart : IsCompStart (P.label s) (arc ++ revWord B.chord)
          (Q.firstPos s) := by
        change IsCompStart (P.label s) B.firstWord (Q.firstPos s)
        exact Q.first_start s hsTarget
      have hnot : ¬ IsComp (P.label s) (arc ++ revWord B.chord)
          (Q.firstPos s) (Q.firstPos s + 1) := by
        change ¬ IsComp (P.label s) B.firstWord
          (Q.firstPos s) (Q.firstPos s + 1)
        exact hExact
      obtain ⟨hseam, hletter, hconnected⟩ :=
        exists_appendSeamPartner_of_not_exact D (P.label s) B.firstBase
          arc (revWord B.chord) (Q.firstPos s) hletters
          (by simpa [hArcLen] using Q.first_pos_lt s hsTarget)
          hsource hstart hnot
      have hchordPos : 0 < B.chord.length := by
        simpa [List.length_append, DGOPolygonCut.length_revWord, hArcLen] using hseam
      let y := B.chord.length - 1
      have hy : y < B.chord.length := by dsimp [y]; omega
      have hpos : B.firstChordPos y = arc.length := by
        simp [BalancedSplitData.firstChordPos, y, hArcLen]
      refine ⟨y, hy, ?_, ?_, ?_⟩
      · simpa only [BalancedSplitData.firstWord, firstHalf, hpos] using hseam
      · simpa only [BalancedSplitData.firstWord, firstHalf, hpos] using hletter
      · simpa only [BalancedSplitData.firstWord, firstHalf, hpos] using hconnected
  · intro s hs
    have hsTarget := (mem_brokenSet_iff.mp hs).1
    have hsNot := (mem_brokenSet_iff.mp hs).2
    have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
      simp [BalancedSplitData.refinedCut, splitPairCut_left B.side_order]
    have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
      simp [BalancedSplitData.refinedCut, splitPairCut_right]
    change ¬ survivesExactly D P.label B.secondBase B.secondWord Q.secondPos s
      at hsNot
    by_cases hExact : IsComp (P.label s) B.secondWord
        (Q.secondPos s) (Q.secondPos s + 1)
    · have hsNotIso : ¬ IsIsolated D.fam (P.label s)
          (vertex P.basepoint P.word B.secondVertex)
          (secondHalf P.word B.refinedCut (B.firstSide + 1)
            (B.secondSide + 2) B.chord) (Q.secondPos s) := by
        intro hiso
        exact hsNot ⟨hExact, by
          simpa [BalancedSplitData.secondBase, BalancedSplitData.secondWord] using
            hiso⟩
      rw [← hright] at hsNotIso
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
        hsNotIso
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
      have hjWordLen := hjlen
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
      have hjLetter : (B.secondWord[j]'hjWordLen).IsCompOf (P.label s) := by
        obtain ⟨jEnd, hjComp⟩ := hjStart
        exact hjComp.2.2.1 j le_rfl hjComp.1 hjWordLen
      refine ⟨y, hy, ?_, ?_, ?_⟩
      · simpa only [hpos] using hjWordLen
      · simpa only [hpos] using hjLetter
      · simpa only [hpos, BalancedSplitData.secondBase,
          BalancedSplitData.secondWord, hright] using hjConn
    · let arc := P.word.drop B.secondVertex ++ P.word.take B.firstVertex
      have hsecondLe : B.secondVertex ≤ P.word.length :=
        by rw [← hright]; exact first_endpoint_le
      have hvorder : B.firstVertex ≤ B.secondVertex := by
        rw [← hleft, ← hright]
        exact split_vertices_ordered
      have hfirstLe : B.firstVertex ≤ P.word.length := hvorder.trans hsecondLe
      have hArcLen : arc.length = B.secondArcLength := by
        simp [arc, List.length_drop, List.length_take, min_eq_left hfirstLe,
          BalancedSplitData.secondArcLength]
      have htake : P.word.take B.firstVertex =
          (P.word.take B.secondVertex).take B.firstVertex := by
        rw [List.take_take, min_eq_left hvorder]
      have hdecomp : rotWord P.word B.secondVertex = arc ++
          (P.word.take B.secondVertex).drop B.firstVertex := by
        calc
          rotWord P.word B.secondVertex =
              P.word.drop B.secondVertex ++ P.word.take B.secondVertex := rfl
          _ = P.word.drop B.secondVertex ++
              ((P.word.take B.secondVertex).take B.firstVertex ++
                (P.word.take B.secondVertex).drop B.firstVertex) := by
                rw [List.take_append_drop]
          _ = arc ++ (P.word.take B.secondVertex).drop B.firstVertex := by
                simp only [arc, ← htake, List.append_assoc]
      have harcEq : arc =
          ((rotWord P.word B.secondVertex).drop 0).take arc.length := by
        rw [List.drop_zero, hdecomp, List.take_left]
      have hsource : IsComp (P.label s) arc
          (Q.secondPos s) (Q.secondPos s + 1) := by
        have hrotLen : (rotWord P.word B.secondVertex).length = P.word.length :=
          length_rotWord P.word hsecondLe
        have hseg := isComp_segment_of_isComp (P.label s)
          (rotWord P.word B.secondVertex) (start := 0) (len := arc.length)
          (i := Q.secondPos s) (finish := Q.secondPos s + 1)
          (by simpa using Q.second_rotated_component s hsTarget)
          (by rw [Nat.zero_add, hArcLen, hrotLen];
              simp only [BalancedSplitData.secondArcLength]; omega)
          (by simpa only [hArcLen] using
            Nat.succ_le_iff.mpr (Q.second_pos_lt s hsTarget))
        rw [harcEq]
        exact hseg
      have hwordEq : B.secondWord = arc ++ B.chord := by
        unfold BalancedSplitData.secondWord secondHalf
        dsimp [arc]
        rw [hleft, hright]
      have hletters : ∀ x ∈ arc ++ B.chord, D.IsLetter x := by
        rw [← hwordEq]
        exact isLetter_secondHalf D P.letters B.chord_geodesic.1
          B.refinedCut (B.firstSide + 1) (B.secondSide + 2)
      have hstart : IsCompStart (P.label s) (arc ++ B.chord)
          (Q.secondPos s) := by
        rw [← hwordEq]
        exact Q.second_start s hsTarget
      have hnot : ¬ IsComp (P.label s) (arc ++ B.chord)
          (Q.secondPos s) (Q.secondPos s + 1) := by
        rw [← hwordEq]
        exact hExact
      obtain ⟨hseam, hletter, hconnected⟩ :=
        exists_appendSeamPartner_of_not_exact D (P.label s) B.secondBase
          arc B.chord (Q.secondPos s) hletters
          (by simpa only [hArcLen] using Q.second_pos_lt s hsTarget)
          hsource hstart hnot
      have hchordPos : 0 < B.chord.length := by
        simpa [List.length_append, hArcLen] using hseam
      let y := 0
      have hy : y < B.chord.length := by dsimp [y]; omega
      have hpos : B.secondChordPos y = arc.length := by
        simp [BalancedSplitData.secondChordPos, y, hArcLen]
      refine ⟨y, hy, ?_, ?_, ?_⟩
      · simpa only [hwordEq, hpos] using hseam
      · simpa only [hwordEq, hpos] using hletter
      · simpa only [hwordEq, hpos] using hconnected

end BalancedSplitArcPlacement

end DGOProposition414
end GGT
end GroupApproximation
