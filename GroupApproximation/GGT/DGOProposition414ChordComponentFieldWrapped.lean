import GroupApproximation.GGT.DGOProposition414ChordComponentField

/-!
# The charged chord component of a wrapped Proposition 4.14 gap child

Wrapped counterpart of `DGOProposition414ChordComponentField`.  The case split
on where the neighbour of a charged partner edge lies is the same, and the one
case left open is again a degenerate right connector with a nonempty inherited
arc, named `SecondGapChordArcSeam`.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-! ## The residual arc/chord seam at a charged partner edge -/

/-- The exclusion of the last inherited arc letter at a charged partner edge
placed second on the child chord, when the right connector degenerates. -/
def SecondGapChordArcSeam
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) : Prop :=
  (B.secondGapRight j).length = 0 →
    0 < (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)).length →
    orientedEdgeIndex (B.secondGapChordStart j) (B.secondGapChordFinish j)
        (B.brokenAssignment.first.partner s) = 0 →
    ∀ hq : (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length - 1 < (B.secondGapCycle j).length,
      ¬ ((B.secondGapCycle j)[(B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length - 1]'hq).IsCompOf (P.label s)

/-- A nonempty right connector makes the charged arc seam vacuous. -/
theorem secondGapChordArcSeam_of_rightConnector
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hright : 0 < (B.secondGapRight j).length) :
    SecondGapChordArcSeam B j s := by
  intro hzero
  exact absurd hzero (by omega)

/-- An empty inherited arc makes the charged arc seam vacuous. -/
theorem secondGapChordArcSeam_of_emptyArc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (harc : (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)).length = 0) :
    SecondGapChordArcSeam B j s := by
  intro _ harcPos
  exact absurd harcPos (by omega)

/-! ## The charged chord component in raw cycle coordinates -/

/-- A charged partner edge is a maximal one-letter component of the auxiliary
cycle, at its raw chord-block position. -/
theorem secondGapChordSource_cycleComponent_raw
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapChordSources j)
    (hseam : SecondGapChordArcSeam B j s) :
    IsComp (P.label s) (B.secondGapCycle j)
      ((B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length +
        orientedEdgeIndex (B.secondGapChordStart j) (B.secondGapChordFinish j)
          (B.brokenAssignment.first.partner s))
      ((B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length +
        orientedEdgeIndex (B.secondGapChordStart j) (B.secondGapChordFinish j)
          (B.brokenAssignment.first.partner s) + 1) := by
  classical
  have hsegComp := B.secondGapChordSource_segmentComponent j s hs
  have hcycleLen : (B.secondGapCycle j).length =
      (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length +
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)).length := by
    simp only [secondGapCycle, auxiliaryCycleWord, List.length_append,
      OsinComponents.length_revWord]
  have hoeiLt : orientedEdgeIndex (B.secondGapChordStart j)
      (B.secondGapChordFinish j) (B.brokenAssignment.first.partner s) <
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j)).length := by
    have h1 := hsegComp.1
    have h2 := hsegComp.2.1
    omega
  have hp : (B.secondGapLeft j).length +
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)).length +
      (B.secondGapRight j).length +
      orientedEdgeIndex (B.secondGapChordStart j) (B.secondGapChordFinish j)
        (B.brokenAssignment.first.partner s) <
      (B.secondGapCycle j).length := by omega
  refine isComp_singleton_of_boundary (P.label s) (B.secondGapCycle j) hp ?_ ?_ ?_
  · exact (isCompOf_auxiliaryCycle_chord_iff (P.label s) (B.secondGapLeft j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)) (B.secondGapRight j)
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j)) _ hoeiLt hp).mpr
      (hsegComp.2.2.1 _ le_rfl (by omega) hoeiLt)
  · intro q hq0 hq hletter
    by_cases hoei : 0 < orientedEdgeIndex (B.secondGapChordStart j)
        (B.secondGapChordFinish j) (B.brokenAssignment.first.partner s)
    · have hidx : q = (B.secondGapLeft j).length +
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)).length +
          (B.secondGapRight j).length +
          (orientedEdgeIndex (B.secondGapChordStart j)
            (B.secondGapChordFinish j)
            (B.brokenAssignment.first.partner s) - 1) := by omega
      have hq' : (B.secondGapLeft j).length +
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)).length +
          (B.secondGapRight j).length +
          (orientedEdgeIndex (B.secondGapChordStart j)
            (B.secondGapChordFinish j)
            (B.brokenAssignment.first.partner s) - 1) <
          (B.secondGapCycle j).length := by omega
      have hgetEq : (B.secondGapCycle j)[q]'hq =
          (B.secondGapCycle j)[(B.secondGapLeft j).length +
            (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
              (B.secondGapFinishSide j)).length +
            (B.secondGapRight j).length +
            (orientedEdgeIndex (B.secondGapChordStart j)
              (B.secondGapChordFinish j)
              (B.brokenAssignment.first.partner s) - 1)]'hq' :=
        getElem_congr_idx hidx
      rw [hgetEq] at hletter
      have hco := (isCompOf_auxiliaryCycle_chord_iff (P.label s)
        (B.secondGapLeft j)
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)) (B.secondGapRight j)
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)) _ (by omega) hq').mp hletter
      exact hsegComp.2.2.2.1 _ (by omega) (by omega) hco
    · have hoei0 : orientedEdgeIndex (B.secondGapChordStart j)
          (B.secondGapChordFinish j)
          (B.brokenAssignment.first.partner s) = 0 := by omega
      have hheadLetter : ((orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j))[0]'(by omega)).IsCompOf (P.label s) := by
        have hh := hsegComp.2.2.1 _ le_rfl (by omega) hoeiLt
        simpa only [hoei0] using hh
      by_cases hright : 0 < (B.secondGapRight j).length
      · have hnxt : HalfGap.nextEntry B.brokenAssignment.index.second j
            ≠ none := by
          intro hnone
          have h0 : (B.secondGapRight j).length = 0 := by
            simp only [secondGapRight]
            rw [hnone]
            simp
          omega
        obtain ⟨e, he'⟩ := Option.ne_none_iff_exists'.mp hnxt
        have he : HalfGap.nextEntry B.brokenAssignment.index.second j =
            some e := by simpa using he'
        have hnotNext := B.secondGap_chordHead_not_isCompOf_nextEntry j e he
          (by omega)
        have hlabelNe : P.label s ≠
            P.label (HalfEntry.entrySource
              B.brokenAssignment.index.second e) := by
          intro hEq
          exact hnotNext (by rw [← hEq]; exact hheadLetter)
        have hqEq : q = (B.secondGapLeft j).length +
            (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
              (B.secondGapFinishSide j)).length +
            ((B.secondGapRight j).length - 1) := by omega
        have hq' : (B.secondGapLeft j).length +
            (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
              (B.secondGapFinishSide j)).length +
            ((B.secondGapRight j).length - 1) <
            (B.secondGapCycle j).length := by omega
        have hconn := B.secondGap_rightConnector_isCompOf j e he
          ((B.secondGapRight j).length - 1) (by omega) hq'
        have hrlab := B.secondGapLocalLabel_rightConnector j e he
          ((B.secondGapRight j).length - 1) (by omega)
        rw [hrlab] at hconn
        have hgetEq : (B.secondGapCycle j)[q]'hq =
            (B.secondGapCycle j)[(B.secondGapLeft j).length +
              (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
                (B.secondGapFinishSide j)).length +
              ((B.secondGapRight j).length - 1)]'hq' :=
          getElem_congr_idx hqEq
        rw [hgetEq] at hletter
        exact hlabelNe (eq_of_isCompOf_of_isCompOf hletter
          (by simpa [List.get_eq_getElem] using hconn))
      · have hR0 : (B.secondGapRight j).length = 0 := by omega
        by_cases harc : 0 < (arcWord B.secondArc B.secondArcCut
            (B.secondGapStartSide j) (B.secondGapFinishSide j)).length
        · have hqEq : q = (B.secondGapLeft j).length +
              (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
                (B.secondGapFinishSide j)).length - 1 := by omega
          have hq' : (B.secondGapLeft j).length +
              (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
                (B.secondGapFinishSide j)).length - 1 <
              (B.secondGapCycle j).length := by omega
          have hgetEq : (B.secondGapCycle j)[q]'hq =
              (B.secondGapCycle j)[(B.secondGapLeft j).length +
                (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
                  (B.secondGapFinishSide j)).length - 1]'hq' :=
            getElem_congr_idx hqEq
          rw [hgetEq] at hletter
          exact hseam hR0 harc hoei0 hq' hletter
        · have hA0 : (arcWord B.secondArc B.secondArcCut
              (B.secondGapStartSide j) (B.secondGapFinishSide j)).length = 0 := by
            omega
          have hleftPos : 0 < (B.secondGapLeft j).length := by omega
          have hone : (B.secondGapLeft j).length = 1 := by
            have hle := B.secondGapLeft_length_le_one j
            omega
          have hqEq : q = 0 := by omega
          have hq' : (0 : ℕ) < (B.secondGapCycle j).length := by omega
          have hgetEq : (B.secondGapCycle j)[q]'hq =
              (B.secondGapCycle j)[0]'hq' := getElem_congr_idx hqEq
          rw [hgetEq] at hletter
          have hconn := B.secondGap_leftConnector_isCompOf j
            (Classical.choose (Option.ne_none_iff_exists'.mp
              (show HalfGap.previousEntry B.brokenAssignment.index.second j
                  ≠ none from by
                intro hnone
                have h0 : (B.secondGapLeft j).length = 0 := by
                  simp only [secondGapLeft]
                  rw [hnone]
                  simp
                omega)))
            (by
              have hspec := Classical.choose_spec
                (Option.ne_none_iff_exists'.mp
                  (show HalfGap.previousEntry B.brokenAssignment.index.second j
                      ≠ none from by
                    intro hnone
                    have h0 : (B.secondGapLeft j).length = 0 := by
                      simp only [secondGapLeft]
                      rw [hnone]
                      simp
                    omega))
              simpa using hspec)
            0 hleftPos hq'
          have hEqLabel : P.label s = B.secondGapLocalLabel j 0 :=
            eq_of_isCompOf_of_isCompOf hletter hconn
          have hn1 : 1 < (B.secondGapCycle j).length := by omega
          have hheadCycle : ((B.secondGapCycle j)[1]'hn1).IsCompOf
              (B.secondGapLocalLabel j 0) := by
            have hidx : (1 : ℕ) = (B.secondGapLeft j).length +
                (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
                  (B.secondGapFinishSide j)).length +
                (B.secondGapRight j).length + 0 := by omega
            have hq'' : (B.secondGapLeft j).length +
                (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
                  (B.secondGapFinishSide j)).length +
                (B.secondGapRight j).length + 0 <
                (B.secondGapCycle j).length := by omega
            have hgetEq2 : (B.secondGapCycle j)[1]'hn1 =
                (B.secondGapCycle j)[(B.secondGapLeft j).length +
                  (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
                    (B.secondGapFinishSide j)).length +
                  (B.secondGapRight j).length + 0]'hq'' :=
              getElem_congr_idx hidx
            rw [hgetEq2, ← hEqLabel]
            exact (isCompOf_auxiliaryCycle_chord_iff (P.label s)
              (B.secondGapLeft j)
              (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
                (B.secondGapFinishSide j)) (B.secondGapRight j)
              (orientedSegment B.chord (B.secondGapChordStart j)
                (B.secondGapChordFinish j)) 0 (by omega) hq'').mpr hheadLetter
          exact B.secondGapLeftConnectorChordSeam_of_left j hleftPos hA0 hR0
            hn1 hheadCycle
  · intro hn hletter
    have hoeiEnd : orientedEdgeIndex (B.secondGapChordStart j)
        (B.secondGapChordFinish j) (B.brokenAssignment.first.partner s) + 1 <
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)).length := by omega
    have hq' : (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length +
        (orientedEdgeIndex (B.secondGapChordStart j) (B.secondGapChordFinish j)
          (B.brokenAssignment.first.partner s) + 1) <
        (B.secondGapCycle j).length := by omega
    have hco := (isCompOf_auxiliaryCycle_chord_iff (P.label s)
      (B.secondGapLeft j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)) (B.secondGapRight j)
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j)) _ hoeiEnd hq').mp hletter
    exact hsegComp.2.2.2.2 hoeiEnd hco

/-! ## The charged chord component field -/

/-- The `chordComponent` field of `SecondGapComponentFamily`, from the residual
arc seam alone. -/
theorem secondGapChordComponentField
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapChordSources j)
    (hseam : SecondGapChordArcSeam B j s) :
    IsComp (B.secondGapLocalLabel j
        (B.secondGapChordTargetIndex j
          (B.brokenAssignment.first.partner s)))
      (B.secondGapCycle j)
      (B.secondGapCut j (B.secondGapChordTargetIndex j
        (B.brokenAssignment.first.partner s)))
      (B.secondGapCut j (B.secondGapChordTargetIndex j
        (B.brokenAssignment.first.partner s) + 1)) := by
  classical
  have harcCut : IsPolygonCut
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j))
      (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j)) :=
    (B.secondArc_isCutPath.arcWord (B.secondGap_side_order j)
      (B.secondGapFinishSide_le j)).cut
  have hcut0 : B.secondGapCut j (B.secondGapChordTargetIndex j
      (B.brokenAssignment.first.partner s)) =
      (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length +
        orientedEdgeIndex (B.secondGapChordStart j) (B.secondGapChordFinish j)
          (B.brokenAssignment.first.partner s) := by
    simp only [secondGapCut, secondGapChordTargetIndex, auxiliaryChordTargetIndex]
    exact auxiliaryCycleCut_chord (B.secondGapLeft j) (B.secondGapRight j) harcCut
  have hidx : B.secondGapChordTargetIndex j
      (B.brokenAssignment.first.partner s) + 1 =
      (B.secondGapLeft j).length +
        (B.secondGapFinishSide j - B.secondGapStartSide j) +
        (B.secondGapRight j).length +
        (orientedEdgeIndex (B.secondGapChordStart j) (B.secondGapChordFinish j)
          (B.brokenAssignment.first.partner s) + 1) := by
    simp only [secondGapChordTargetIndex, auxiliaryChordTargetIndex]
    omega
  have hcut1 : B.secondGapCut j (B.secondGapChordTargetIndex j
      (B.brokenAssignment.first.partner s) + 1) =
      (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length +
        (orientedEdgeIndex (B.secondGapChordStart j) (B.secondGapChordFinish j)
          (B.brokenAssignment.first.partner s) + 1) := by
    rw [hidx]
    simp only [secondGapCut]
    exact auxiliaryCycleCut_chord (B.secondGapLeft j) (B.secondGapRight j) harcCut
  rw [B.secondGapLocalLabel_chord j s hs, hcut0, hcut1]
  exact B.secondGapChordSource_cycleComponent_raw j s hs hseam

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
