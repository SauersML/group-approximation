import GroupApproximation.GGT.DGOProposition414GapSurvivors
import GroupApproximation.GGT.OsinTheorem54SepSegmentComp

/-!
# Maximal components in the restricted balanced-split arcs

Taking a subword cannot enlarge a component whose entire span is retained.
This file records the boundary-inclusive restriction lemma and applies it to
the inherited distinguished one-edge components in every canonical gap.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace OsinComponents

omit [Group G] in
/-- A component of a word remains a component of a segment containing its
whole span.  Unlike the converse transfer, both segment boundary cases are
automatic: at an exposed endpoint the corresponding maximality clause is
vacuous. -/
theorem isComp_segment_of_isComp (lam : Λ) (word : List (RelLetter G Λ))
    {start len i finish : ℕ}
    (hcomp : IsComp lam word (start + i) (start + finish))
    (hstart : start + len ≤ word.length)
    (hfinish : finish ≤ len) :
    IsComp lam ((word.drop start).take len) i finish := by
  obtain ⟨hif, hflen, hrange, hprev, hnext⟩ := hcomp
  have hseglen : ((word.drop start).take len).length = len := by
    rw [List.length_take, List.length_drop]
    omega
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro q hiq hqf hq
    have hword : start + q < word.length := by omega
    rw [← getElem_segment' word start len q (start + q) hq hword rfl]
    exact hrange (start + q) (by omega) (by omega) hword
  · intro q heq hq hletter
    have hword : start + q < word.length := by omega
    rw [← getElem_segment' word start len q (start + q) hq hword rfl] at hletter
    exact hprev (start + q) (by omega) hword hletter
  · intro hf hletter
    have hword : start + finish < word.length := by omega
    rw [← getElem_segment' word start len finish (start + finish) hf hword rfl]
      at hletter
    exact hnext hword hletter

end OsinComponents

namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

/-- A component occupying one retained side of a cut path remains maximal in
the subarc between any two surrounding side cuts. -/
theorem isComp_arcWord_of_isComp
    {D : RelGenSet G Λ} {b : ℝ} {sideCount : ℕ} {base : G}
    {word : List (RelLetter G Λ)} {cut : ℕ → ℕ}
    (path : IsCutPath D b sideCount base word cut)
    (lam : Λ) {first side last : ℕ}
    (hfirst : first ≤ side) (hlast : side + 1 ≤ last)
    (hlastCount : last ≤ sideCount)
    (hcomp : IsComp lam word (cut side) (cut (side + 1))) :
    IsComp lam (arcWord word cut first last)
      (cut side - cut first) (cut (side + 1) - cut first) := by
  have hfirstCut : cut first ≤ cut side := path.cut.mono_le hfirst
  have hfinishCut : cut first ≤ cut (side + 1) :=
    path.cut.mono_le (by omega)
  have hlastCut : cut first ≤ cut last :=
    path.cut.mono_le (by omega)
  have hsideLast : cut (side + 1) ≤ cut last := path.cut.mono_le hlast
  have hlastLen : cut last ≤ word.length := path.cut.le_length hlastCount
  have hcomp' : IsComp lam word
      (cut first + (cut side - cut first))
      (cut first + (cut (side + 1) - cut first)) := by
    simpa [Nat.add_sub_of_le hfirstCut, Nat.add_sub_of_le hfinishCut] using hcomp
  have hsegment := isComp_segment_of_isComp lam word hcomp'
    (len := cut last - cut first)
    (by simpa [Nat.add_sub_of_le hlastCut] using hlastLen)
    (by omega)
  exact hsegment

namespace BalancedSplitData

/-- An inherited first-half target is still its exact one-edge maximal
component in the open first arc. -/
theorem firstArc_targetComponent
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.firstTarget) :
    IsComp (P.label s) B.firstArc
      (B.firstTargetPos s) (B.firstTargetPos s + 1) := by
  have hsecondLe : B.secondVertex ≤ P.word.length :=
    B.secondVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
  have hstart : B.firstVertex + (B.secondVertex - B.firstVertex) ≤
      P.word.length := by
    have := B.split_vertices_ordered
    omega
  have hend : B.firstTargetPos s + 1 ≤
      B.secondVertex - B.firstVertex := by
    simpa only [firstArcLength] using Nat.succ_le_iff.mpr (B.firstTargetPos_lt hs)
  have hcomp := isComp_segment_of_isComp (P.label s) P.word
    (B.first_original_component hs) hstart hend
  unfold firstArc arcWord
  rw [show B.refinedCut (B.firstSide + 1) = B.firstVertex by
        simp [BalancedSplitData.refinedCut, splitPairCut_left B.side_order],
    show B.refinedCut (B.secondSide + 2) = B.secondVertex by
        simp [BalancedSplitData.refinedCut, splitPairCut_right]]
  exact hcomp

/-- An inherited wrapped-half target is still its exact one-edge maximal
component in the open wrapped arc. -/
theorem secondArc_targetComponent
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.secondTarget) :
    IsComp (P.label s) B.secondArc
      (B.secondTargetPos s) (B.secondTargetPos s + 1) := by
  have hsecondLe : B.secondVertex ≤ P.word.length :=
    B.secondVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
  have hfirstLe : B.firstVertex ≤ P.word.length :=
    B.split_vertices_ordered.trans hsecondLe
  have hlen : B.secondArc.length = B.secondArcLength := by
    rw [secondArc, List.length_append, List.length_drop, List.length_take]
    simp only [secondArcLength]
    omega
  have hend : B.secondTargetPos s + 1 ≤ B.secondArc.length := by
    have hcut := (B.secondArcCut_target hs).2
    have hle := B.secondArc_isCutPath.cut.le_length
      (show B.secondTargetSide s + 1 ≤
          (n - B.secondSide) + B.firstSide + 1 by
        exact Nat.succ_le_iff.mpr (B.secondTargetSide_lt hs))
    rw [hcut] at hle
    exact hle
  have hrotlen : (rotWord P.word B.secondVertex).length = P.word.length := by
    exact length_rotWord P.word hsecondLe
  have hcomp := isComp_segment_of_isComp (P.label s)
    (rotWord P.word B.secondVertex) (start := 0)
    (len := B.secondArc.length) (i := B.secondTargetPos s)
    (finish := B.secondTargetPos s + 1)
    (by simpa using B.second_rotated_component hs)
    (by
      rw [Nat.zero_add]
      calc
        B.secondArc.length = B.secondArcLength := hlen
        _ ≤ P.word.length := by
          simp only [secondArcLength]
          have := B.split_vertices_ordered
          omega
        _ = (rotWord P.word B.secondVertex).length := hrotlen.symm) hend
  have harc : B.secondArc =
      ((rotWord P.word B.secondVertex).drop 0).take B.secondArc.length := by
    rw [List.drop_zero]
    have htake : P.word.take B.firstVertex =
        (P.word.take B.secondVertex).take B.firstVertex := by
      rw [List.take_take, min_eq_left B.split_vertices_ordered]
    have hdecomp : rotWord P.word B.secondVertex = B.secondArc ++
        (P.word.take B.secondVertex).drop B.firstVertex := by
      calc
        rotWord P.word B.secondVertex =
            P.word.drop B.secondVertex ++ P.word.take B.secondVertex := rfl
        _ = P.word.drop B.secondVertex ++
            ((P.word.take B.secondVertex).take B.firstVertex ++
              (P.word.take B.secondVertex).drop B.firstVertex) := by
              rw [List.take_append_drop]
        _ = (P.word.drop B.secondVertex ++ P.word.take B.firstVertex) ++
            (P.word.take B.secondVertex).drop B.firstVertex := by
              rw [← htake, List.append_assoc]
        _ = B.secondArc ++
            (P.word.take B.secondVertex).drop B.firstVertex := by
              rfl
    rw [hdecomp, List.take_left]
  rw [harc]
  exact hcomp

/-- The exact inherited component in a canonical first-half gap subarc. -/
theorem firstGapArcSource_component
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j) :
    IsComp (P.label s)
      (arcWord B.firstArc B.firstArcCut
        (B.firstGapStartSide j) (B.firstGapFinishSide j))
      (B.firstArcCut (B.firstTargetSide s) -
        B.firstArcCut (B.firstGapStartSide j))
      (B.firstArcCut (B.firstTargetSide s) -
        B.firstArcCut (B.firstGapStartSide j) + 1) := by
  have hsData := Finset.mem_filter.mp hs
  have hcomp := B.firstArc_targetComponent hsData.1
  have hcut := B.firstArcCut_target hsData.1
  have hcompCut : IsComp (P.label s) B.firstArc
      (B.firstArcCut (B.firstTargetSide s))
      (B.firstArcCut (B.firstTargetSide s + 1)) := by
    simpa only [hcut.1, hcut.2] using hcomp
  have hrestricted := isComp_arcWord_of_isComp B.firstArc_isCutPath
    (P.label s) hsData.2.1 (Nat.succ_le_iff.mpr hsData.2.2)
    (B.firstGapFinishSide_le j) hcompCut
  have hbase : B.firstArcCut (B.firstGapStartSide j) ≤
      B.firstTargetPos s := by
    rw [← hcut.1]
    exact B.firstArc_isCutPath.cut.mono_le hsData.2.1
  convert hrestricted using 1
  all_goals simp only [hcut.1, hcut.2]
  all_goals omega

/-- The exact inherited component in a canonical wrapped-half gap subarc. -/
theorem secondGapArcSource_component
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j) :
    IsComp (P.label s)
      (arcWord B.secondArc B.secondArcCut
        (B.secondGapStartSide j) (B.secondGapFinishSide j))
      (B.secondArcCut (B.secondTargetSide s) -
        B.secondArcCut (B.secondGapStartSide j))
      (B.secondArcCut (B.secondTargetSide s) -
        B.secondArcCut (B.secondGapStartSide j) + 1) := by
  have hsData := Finset.mem_filter.mp hs
  have hcomp := B.secondArc_targetComponent hsData.1
  have hcut := B.secondArcCut_target hsData.1
  have hcompCut : IsComp (P.label s) B.secondArc
      (B.secondArcCut (B.secondTargetSide s))
      (B.secondArcCut (B.secondTargetSide s + 1)) := by
    simpa only [hcut.1, hcut.2] using hcomp
  have hrestricted := isComp_arcWord_of_isComp B.secondArc_isCutPath
    (P.label s) hsData.2.1 (Nat.succ_le_iff.mpr hsData.2.2)
    (B.secondGapFinishSide_le j) hcompCut
  have hbase : B.secondArcCut (B.secondGapStartSide j) ≤
      B.secondTargetPos s := by
    rw [← hcut.1]
    exact B.secondArc_isCutPath.cut.mono_le hsData.2.1
  convert hrestricted using 1
  all_goals simp only [hcut.1, hcut.2]
  all_goals omega

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
