import GroupApproximation.GGT.DGOProposition414LeftChordSeamProofWrapped

/-!
# The charged chord component of a Proposition 4.14 gap child

The sides of type (4) in Dahmani--Guirardel--Osin's auxiliary cycle are the
partner edges `y_j` of the broken sources of the opposite half.  Their
maximality in `c_j` is proved here: away from the two ends of the child chord
it is the landed interior transfer, at the far end it is vacuous because the
chord block closes the cycle, and at the near end the neighbour is the right
connector or, when that degenerates, the left connector, both excluded by the
seam lemmas already available.

The single case left open is a degenerate right connector with a nonempty
inherited arc, where the neighbour is the last arc letter; that is DGO's

> `y_j` can not be connected to a component of a side of type (2) since
> otherwise `p_{i_j}` is not isolated in `\mathcal P`

(arXiv:1111.7048, proof of Proposition 4.14), and it is named here as
`FirstGapChordArcSeam`.
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
placed first on the child chord, when the right connector degenerates. -/
def FirstGapChordArcSeam
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) : Prop :=
  (B.firstGapRight j).length = 0 →
    0 < (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)).length →
    orientedEdgeIndex (B.firstGapChordStart j) (B.firstGapChordFinish j)
        (B.brokenAssignment.second.partner s) = 0 →
    ∀ hq : (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length - 1 < (B.firstGapCycle j).length,
      ¬ ((B.firstGapCycle j)[(B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length - 1]'hq).IsCompOf (P.label s)

/-- A nonempty right connector makes the charged arc seam vacuous. -/
theorem firstGapChordArcSeam_of_rightConnector
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hright : 0 < (B.firstGapRight j).length) :
    FirstGapChordArcSeam B j s := by
  intro hzero
  exact absurd hzero (by omega)

/-- An empty inherited arc makes the charged arc seam vacuous. -/
theorem firstGapChordArcSeam_of_emptyArc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (harc : (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)).length = 0) :
    FirstGapChordArcSeam B j s := by
  intro _ harcPos
  exact absurd harcPos (by omega)

/-! ## The charged chord component in raw cycle coordinates -/

/-- A charged partner edge is a maximal one-letter component of the auxiliary
cycle, at its raw chord-block position. -/
theorem firstGapChordSource_cycleComponent_raw
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapChordSources j)
    (hseam : FirstGapChordArcSeam B j s) :
    IsComp (P.label s) (B.firstGapCycle j)
      ((B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length +
        orientedEdgeIndex (B.firstGapChordStart j) (B.firstGapChordFinish j)
          (B.brokenAssignment.second.partner s))
      ((B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length +
        orientedEdgeIndex (B.firstGapChordStart j) (B.firstGapChordFinish j)
          (B.brokenAssignment.second.partner s) + 1) := by
  classical
  have hsegComp := B.firstGapChordSource_segmentComponent j s hs
  have hcycleLen : (B.firstGapCycle j).length =
      (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length +
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)).length := by
    simp only [firstGapCycle, auxiliaryCycleWord, List.length_append,
      OsinComponents.length_revWord]
  have hoeiLt : orientedEdgeIndex (B.firstGapChordStart j)
      (B.firstGapChordFinish j) (B.brokenAssignment.second.partner s) <
      (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j)).length := by
    have h1 := hsegComp.1
    have h2 := hsegComp.2.1
    omega
  have hp : (B.firstGapLeft j).length +
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)).length +
      (B.firstGapRight j).length +
      orientedEdgeIndex (B.firstGapChordStart j) (B.firstGapChordFinish j)
        (B.brokenAssignment.second.partner s) <
      (B.firstGapCycle j).length := by omega
  refine isComp_singleton_of_boundary (P.label s) (B.firstGapCycle j) hp ?_ ?_ ?_
  · exact (isCompOf_auxiliaryCycle_chord_iff (P.label s) (B.firstGapLeft j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)) (B.firstGapRight j)
      (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j)) _ hoeiLt hp).mpr
      (hsegComp.2.2.1 _ le_rfl (by omega) hoeiLt)
  · intro q hq0 hq hletter
    by_cases hoei : 0 < orientedEdgeIndex (B.firstGapChordStart j)
        (B.firstGapChordFinish j) (B.brokenAssignment.second.partner s)
    · have hidx : q = (B.firstGapLeft j).length +
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)).length +
          (B.firstGapRight j).length +
          (orientedEdgeIndex (B.firstGapChordStart j)
            (B.firstGapChordFinish j)
            (B.brokenAssignment.second.partner s) - 1) := by omega
      have hq' : (B.firstGapLeft j).length +
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)).length +
          (B.firstGapRight j).length +
          (orientedEdgeIndex (B.firstGapChordStart j)
            (B.firstGapChordFinish j)
            (B.brokenAssignment.second.partner s) - 1) <
          (B.firstGapCycle j).length := by omega
      have hgetEq : (B.firstGapCycle j)[q]'hq =
          (B.firstGapCycle j)[(B.firstGapLeft j).length +
            (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
              (B.firstGapFinishSide j)).length +
            (B.firstGapRight j).length +
            (orientedEdgeIndex (B.firstGapChordStart j)
              (B.firstGapChordFinish j)
              (B.brokenAssignment.second.partner s) - 1)]'hq' :=
        getElem_congr_idx hidx
      rw [hgetEq] at hletter
      have hco := (isCompOf_auxiliaryCycle_chord_iff (P.label s)
        (B.firstGapLeft j)
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)) (B.firstGapRight j)
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)) _ (by omega) hq').mp hletter
      exact hsegComp.2.2.2.1 _ (by omega) (by omega) hco
    · have hoei0 : orientedEdgeIndex (B.firstGapChordStart j)
          (B.firstGapChordFinish j)
          (B.brokenAssignment.second.partner s) = 0 := by omega
      have hheadLetter : ((orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j))[0]'(by omega)).IsCompOf (P.label s) := by
        have hh := hsegComp.2.2.1 _ le_rfl (by omega) hoeiLt
        simpa only [hoei0] using hh
      by_cases hright : 0 < (B.firstGapRight j).length
      · have hnxt : HalfGap.nextEntry B.brokenAssignment.index.first j
            ≠ none := by
          intro hnone
          have h0 : (B.firstGapRight j).length = 0 := by
            simp only [firstGapRight]
            rw [hnone]
            simp
          omega
        obtain ⟨e, he'⟩ := Option.ne_none_iff_exists'.mp hnxt
        have he : HalfGap.nextEntry B.brokenAssignment.index.first j =
            some e := by simpa using he'
        have hnotNext := B.firstGap_chordHead_not_isCompOf_nextEntry j e he
          (by omega)
        have hlabelNe : P.label s ≠
            P.label (HalfEntry.entrySource
              B.brokenAssignment.index.first e) := by
          intro hEq
          exact hnotNext (by rw [← hEq]; exact hheadLetter)
        have hqEq : q = (B.firstGapLeft j).length +
            (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
              (B.firstGapFinishSide j)).length +
            ((B.firstGapRight j).length - 1) := by omega
        have hq' : (B.firstGapLeft j).length +
            (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
              (B.firstGapFinishSide j)).length +
            ((B.firstGapRight j).length - 1) <
            (B.firstGapCycle j).length := by omega
        have hconn := B.firstGap_rightConnector_isCompOf j e he
          ((B.firstGapRight j).length - 1) (by omega) hq'
        have hrlab := B.firstGapLocalLabel_rightConnector j e he
          ((B.firstGapRight j).length - 1) (by omega)
        rw [hrlab] at hconn
        have hgetEq : (B.firstGapCycle j)[q]'hq =
            (B.firstGapCycle j)[(B.firstGapLeft j).length +
              (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
                (B.firstGapFinishSide j)).length +
              ((B.firstGapRight j).length - 1)]'hq' :=
          getElem_congr_idx hqEq
        rw [hgetEq] at hletter
        exact hlabelNe (eq_of_isCompOf_of_isCompOf hletter
          (by simpa [List.get_eq_getElem] using hconn))
      · have hR0 : (B.firstGapRight j).length = 0 := by omega
        by_cases harc : 0 < (arcWord B.firstArc B.firstArcCut
            (B.firstGapStartSide j) (B.firstGapFinishSide j)).length
        · have hqEq : q = (B.firstGapLeft j).length +
              (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
                (B.firstGapFinishSide j)).length - 1 := by omega
          have hq' : (B.firstGapLeft j).length +
              (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
                (B.firstGapFinishSide j)).length - 1 <
              (B.firstGapCycle j).length := by omega
          have hgetEq : (B.firstGapCycle j)[q]'hq =
              (B.firstGapCycle j)[(B.firstGapLeft j).length +
                (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
                  (B.firstGapFinishSide j)).length - 1]'hq' :=
            getElem_congr_idx hqEq
          rw [hgetEq] at hletter
          exact hseam hR0 harc hoei0 hq' hletter
        · have hA0 : (arcWord B.firstArc B.firstArcCut
              (B.firstGapStartSide j) (B.firstGapFinishSide j)).length = 0 := by
            omega
          have hleftPos : 0 < (B.firstGapLeft j).length := by omega
          have hone : (B.firstGapLeft j).length = 1 := by
            have hle := B.firstGapLeft_length_le_one j
            omega
          have hqEq : q = 0 := by omega
          have hq' : (0 : ℕ) < (B.firstGapCycle j).length := by omega
          have hgetEq : (B.firstGapCycle j)[q]'hq =
              (B.firstGapCycle j)[0]'hq' := getElem_congr_idx hqEq
          rw [hgetEq] at hletter
          have hconn := B.firstGap_leftConnector_isCompOf j
            (Classical.choose (Option.ne_none_iff_exists'.mp
              (show HalfGap.previousEntry B.brokenAssignment.index.first j
                  ≠ none from by
                intro hnone
                have h0 : (B.firstGapLeft j).length = 0 := by
                  simp only [firstGapLeft]
                  rw [hnone]
                  simp
                omega)))
            (by
              have hspec := Classical.choose_spec
                (Option.ne_none_iff_exists'.mp
                  (show HalfGap.previousEntry B.brokenAssignment.index.first j
                      ≠ none from by
                    intro hnone
                    have h0 : (B.firstGapLeft j).length = 0 := by
                      simp only [firstGapLeft]
                      rw [hnone]
                      simp
                    omega))
              simpa using hspec)
            0 hleftPos hq'
          have hEqLabel : P.label s = B.firstGapLocalLabel j 0 :=
            eq_of_isCompOf_of_isCompOf hletter hconn
          have hn1 : 1 < (B.firstGapCycle j).length := by omega
          have hheadCycle : ((B.firstGapCycle j)[1]'hn1).IsCompOf
              (B.firstGapLocalLabel j 0) := by
            have hidx : (1 : ℕ) = (B.firstGapLeft j).length +
                (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
                  (B.firstGapFinishSide j)).length +
                (B.firstGapRight j).length + 0 := by omega
            have hq'' : (B.firstGapLeft j).length +
                (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
                  (B.firstGapFinishSide j)).length +
                (B.firstGapRight j).length + 0 <
                (B.firstGapCycle j).length := by omega
            have hgetEq2 : (B.firstGapCycle j)[1]'hn1 =
                (B.firstGapCycle j)[(B.firstGapLeft j).length +
                  (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
                    (B.firstGapFinishSide j)).length +
                  (B.firstGapRight j).length + 0]'hq'' :=
              getElem_congr_idx hidx
            rw [hgetEq2, ← hEqLabel]
            exact (isCompOf_auxiliaryCycle_chord_iff (P.label s)
              (B.firstGapLeft j)
              (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
                (B.firstGapFinishSide j)) (B.firstGapRight j)
              (orientedSegment B.chord (B.firstGapChordStart j)
                (B.firstGapChordFinish j)) 0 (by omega) hq'').mpr hheadLetter
          exact B.firstGapLeftConnectorChordSeam_of_left j hleftPos hA0 hR0
            hn1 hheadCycle
  · intro hn hletter
    have hoeiEnd : orientedEdgeIndex (B.firstGapChordStart j)
        (B.firstGapChordFinish j) (B.brokenAssignment.second.partner s) + 1 <
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)).length := by omega
    have hq' : (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length +
        (orientedEdgeIndex (B.firstGapChordStart j) (B.firstGapChordFinish j)
          (B.brokenAssignment.second.partner s) + 1) <
        (B.firstGapCycle j).length := by omega
    have hco := (isCompOf_auxiliaryCycle_chord_iff (P.label s)
      (B.firstGapLeft j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)) (B.firstGapRight j)
      (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j)) _ hoeiEnd hq').mp hletter
    exact hsegComp.2.2.2.2 hoeiEnd hco

/-! ## The charged chord component field -/

/-- The `chordComponent` field of `FirstGapComponentFamily`, from the residual
arc seam alone. -/
theorem firstGapChordComponentField
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapChordSources j)
    (hseam : FirstGapChordArcSeam B j s) :
    IsComp (B.firstGapLocalLabel j
        (B.firstGapChordTargetIndex j
          (B.brokenAssignment.second.partner s)))
      (B.firstGapCycle j)
      (B.firstGapCut j (B.firstGapChordTargetIndex j
        (B.brokenAssignment.second.partner s)))
      (B.firstGapCut j (B.firstGapChordTargetIndex j
        (B.brokenAssignment.second.partner s) + 1)) := by
  classical
  have harcCut : IsPolygonCut
      (B.firstGapFinishSide j - B.firstGapStartSide j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j))
      (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j)) :=
    (B.firstArc_isCutPath.arcWord (B.firstGap_side_order j)
      (B.firstGapFinishSide_le j)).cut
  have hcut0 : B.firstGapCut j (B.firstGapChordTargetIndex j
      (B.brokenAssignment.second.partner s)) =
      (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length +
        orientedEdgeIndex (B.firstGapChordStart j) (B.firstGapChordFinish j)
          (B.brokenAssignment.second.partner s) := by
    simp only [firstGapCut, firstGapChordTargetIndex, auxiliaryChordTargetIndex]
    exact auxiliaryCycleCut_chord (B.firstGapLeft j) (B.firstGapRight j) harcCut
  have hidx : B.firstGapChordTargetIndex j
      (B.brokenAssignment.second.partner s) + 1 =
      (B.firstGapLeft j).length +
        (B.firstGapFinishSide j - B.firstGapStartSide j) +
        (B.firstGapRight j).length +
        (orientedEdgeIndex (B.firstGapChordStart j) (B.firstGapChordFinish j)
          (B.brokenAssignment.second.partner s) + 1) := by
    simp only [firstGapChordTargetIndex, auxiliaryChordTargetIndex]
    omega
  have hcut1 : B.firstGapCut j (B.firstGapChordTargetIndex j
      (B.brokenAssignment.second.partner s) + 1) =
      (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length +
        (orientedEdgeIndex (B.firstGapChordStart j) (B.firstGapChordFinish j)
          (B.brokenAssignment.second.partner s) + 1) := by
    rw [hidx]
    simp only [firstGapCut]
    exact auxiliaryCycleCut_chord (B.firstGapLeft j) (B.firstGapRight j) harcCut
  rw [B.firstGapLocalLabel_chord j s hs, hcut0, hcut1]
  exact B.firstGapChordSource_cycleComponent_raw j s hs hseam

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
