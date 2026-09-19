import GroupApproximation.GGT.DGOProposition414ArcChordSeamProof

/-!
# The degenerate arc/chord seam of a wrapped Proposition 4.14 gap child

Wrapped counterpart of `DGOProposition414ArcChordSeamProof`.  The wrapped half
reads the chord forwards, so the two orientation branches exchange which
endpoint of the child chord the degenerate connector identifies with the
terminal vertex of the retained source; the isolation argument is the same.
With this the inherited-arc component field of both gap component families is
unconditional.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-! ## Isolation of a surviving wrapped source -/

/-- Wrapped counterpart of `firstSurvivor_not_isCompOf_of_vertex_eq`. -/
theorem secondSurvivor_not_isCompOf_of_vertex_eq
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hsurv : B.componentPlacement.secondSurvives s)
    (m z : ℕ) (hmlt : m < B.secondWord.length)
    (hzle : z ≤ B.secondWord.length) (hmz : m ≤ z) (hzm : z ≤ m + 1)
    (hpos : B.secondTargetPos s < m)
    (hvert : vertex B.secondBase B.secondWord (B.secondTargetPos s + 1) =
      vertex B.secondBase B.secondWord z) :
    ¬ (B.secondWord[m]'hmlt).IsCompOf (P.label s) := by
  intro hletter
  have hcompS : IsComp (P.label s) B.secondWord (B.secondTargetPos s)
      (B.secondTargetPos s + 1) := hsurv.1
  have hisoS : IsIsolated D.fam (P.label s) B.secondBase B.secondWord
      (B.secondTargetPos s) := hsurv.2
  obtain ⟨a, bb, ha, hb, hcomp⟩ :=
    exists_isComp_of_isCompOf (P.label s) B.secondWord m hmlt hletter
  have hspan : (vertex B.secondBase B.secondWord a)⁻¹ *
      vertex B.secondBase B.secondWord z ∈ D.fam (P.label s) :=
    span_mem_fam D (P.label s) B.secondBase B.secondWord_letters z hzle a
      (by omega) (fun q hq1 hq2 hq => hcomp.2.2.1 q hq1 (by omega) hq)
  have hspanS : (vertex B.secondBase B.secondWord (B.secondTargetPos s))⁻¹ *
      vertex B.secondBase B.secondWord (B.secondTargetPos s + 1) ∈
      D.fam (P.label s) :=
    span_mem_fam_of_isComp D B.secondBase B.secondWord_letters hcompS
  have hconn : Connected D.fam (P.label s) B.secondBase B.secondWord
      (B.secondTargetPos s) a := by
    show (vertex B.secondBase B.secondWord (B.secondTargetPos s))⁻¹ *
      vertex B.secondBase B.secondWord a ∈ D.fam (P.label s)
    have hfac : (vertex B.secondBase B.secondWord (B.secondTargetPos s))⁻¹ *
        vertex B.secondBase B.secondWord a =
        ((vertex B.secondBase B.secondWord (B.secondTargetPos s))⁻¹ *
            vertex B.secondBase B.secondWord (B.secondTargetPos s + 1)) *
          ((vertex B.secondBase B.secondWord a)⁻¹ *
            vertex B.secondBase B.secondWord z)⁻¹ := by
      rw [hvert]
      group
    rw [hfac]
    exact mul_mem hspanS (inv_mem hspan)
  have hane : a ≠ B.secondTargetPos s := by
    intro heq
    have hlt : B.secondTargetPos s + 1 < B.secondWord.length := by omega
    have hin : (B.secondWord[B.secondTargetPos s + 1]'hlt).IsCompOf
        (P.label s) :=
      hcomp.2.2.1 (B.secondTargetPos s + 1) (by omega) (by omega) hlt
    exact hcompS.2.2.2.2 hlt hin
  exact hisoS.2 a hane ⟨bb, hcomp⟩ hconn

/-! ## Which connector a wrapped gap carries -/

/-- A forward wrapped gap carries the compressed through-partner connector of
its following broken source. -/
theorem secondGapRight_of_next_forward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.second j = some e)
    (hfwd : B.secondGapRunsForward j) :
    B.secondGapRight j =
      (B.secondBrokenConnectors
        (HalfEntry.entrySource B.brokenAssignment.index.second e)
        (HalfEntry.entrySource_mem
          B.brokenAssignment.index.second e)).startThroughPartner := by
  classical
  simp only [secondGapRight]
  rw [he]
  simp [hfwd]

/-- A backward wrapped gap carries the start connector of its following broken
source. -/
theorem secondGapRight_of_next_backward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.second j = some e)
    (hfwd : ¬ B.secondGapRunsForward j) :
    B.secondGapRight j =
      (B.secondBrokenConnectors
        (HalfEntry.entrySource B.brokenAssignment.index.second e)
        (HalfEntry.entrySource_mem
          B.brokenAssignment.index.second e)).startConnector := by
  classical
  simp only [secondGapRight]
  rw [he]
  simp [hfwd]

/-! ## The wrapped gap arc ends at the next broken source -/

/-- Wrapped counterpart of `firstGapArcSource_terminal_pos_succ`. -/
theorem secondGapArcSource_terminal_pos_succ
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.second j = some e)
    (hterminal :
      B.secondArcCut (B.secondTargetSide s) -
          B.secondArcCut (B.secondGapStartSide j) + 1 =
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length) :
    B.secondTargetPos s + 1 =
      B.secondTargetPos (HalfEntry.entrySource
        B.brokenAssignment.index.second e) := by
  have hsData := Finset.mem_filter.mp hs
  have htBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.second e
  have htTarget := (mem_brokenSet_iff.mp htBroken).1
  have hcutEnd : B.secondArcCut (B.secondGapFinishSide j) ≤
      B.secondArc.length :=
    B.secondArc_isCutPath.cut.le_length (B.secondGapFinishSide_le j)
  have harcLen : (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)).length =
      B.secondArcCut (B.secondGapFinishSide j) -
        B.secondArcCut (B.secondGapStartSide j) :=
    length_arcWord B.secondArc B.secondArcCut hcutEnd
  have hfinishSide : B.secondGapFinishSide j =
      B.secondTargetSide (HalfEntry.entrySource
        B.brokenAssignment.index.second e) := by
    simp only [secondGapFinishSide]
    rw [he]
  have hposT : B.secondArcCut (B.secondGapFinishSide j) =
      B.secondTargetPos (HalfEntry.entrySource
        B.brokenAssignment.index.second e) := by
    rw [hfinishSide, (B.secondArcCut_target htTarget).1]
  have hposS : B.secondArcCut (B.secondTargetSide s) = B.secondTargetPos s :=
    (B.secondArcCut_target hsData.1).1
  have hstartLe : B.secondArcCut (B.secondGapStartSide j) ≤
      B.secondArcCut (B.secondTargetSide s) :=
    B.secondArc_isCutPath.cut.mono_le hsData.2.1
  rw [← hposS, ← hposT]
  omega

/-! ## The wrapped seam, closed -/

/-- Wrapped counterpart of `firstGapArcChordSeam_of_source`. -/
theorem secondGapArcChordSeam_of_source
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j) :
    SecondGapArcChordSeam B j s := by
  classical
  by_cases hnone : HalfGap.nextEntry B.brokenAssignment.index.second j = none
  · exact secondGapArcChordSeam_of_lastGap B j s hs hnone
  · obtain ⟨e, he'⟩ := Option.ne_none_iff_exists'.mp hnone
    have he : HalfGap.nextEntry B.brokenAssignment.index.second j =
        some e := by simpa using he'
    intro hright0 hterminal hn hletter
    have hsData := Finset.mem_filter.mp hs
    have htBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.second e
    have hsurv := B.secondGapArcSource_survives j s hs
    have hadj := B.secondGapArcSource_terminal_pos_succ j s hs e he hterminal
    have hpartnerLt : B.brokenAssignment.second.partner
        (HalfEntry.entrySource B.brokenAssignment.index.second e) <
        B.chord.length :=
      B.brokenAssignment.second.partner_lt _ htBroken
    have hposSlt : B.secondTargetPos s < B.secondArcLength :=
      B.secondTargetPos_lt hsData.1
    have hcycleLen : (B.secondGapCycle j).length =
        (B.secondGapLeft j).length +
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)).length +
          (B.secondGapRight j).length +
          (orientedSegment B.chord (B.secondGapChordStart j)
            (B.secondGapChordFinish j)).length := by
      simp only [secondGapCycle, auxiliaryCycleWord, List.length_append,
        OsinComponents.length_revWord]
    have hsegPos : 0 < (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j)).length := by omega
    have hn' : (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length + 0 <
        (B.secondGapCycle j).length := by omega
    have hgetEq : (B.secondGapCycle j)[(B.secondGapLeft j).length +
          (B.secondArcCut (B.secondTargetSide s) -
            B.secondArcCut (B.secondGapStartSide j)) + 1]'hn =
        (B.secondGapCycle j)[(B.secondGapLeft j).length +
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)).length +
          (B.secondGapRight j).length + 0]'hn' :=
      getElem_congr_idx (by omega)
    rw [hgetEq] at hletter
    have hchordHead := (isCompOf_auxiliaryCycle_chord_iff (P.label s)
      (B.secondGapLeft j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)) (B.secondGapRight j)
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j)) 0 hsegPos hn').mp hletter
    by_cases hfwd : B.secondGapRunsForward j
    · have hfinishGe : B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second e) + 1 ≤
          B.secondGapChordFinish j := by
        cases hp : HalfGap.previousEntry B.brokenAssignment.index.second j with
        | none =>
            rw [B.secondGapChordFinish_of_prev_none j hp]
            omega
        | some p =>
            have hlt :=
              (B.secondGapRunsForward_iff_of_adjacent j p e hp he).mp hfwd
            rw [B.secondGapChordFinish_of_prev_forward j p hp hfwd]
            omega
      have hy : B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second e) + 1 <
          B.chord.length := by
        have hcf : B.secondGapChordFinish j ≤ B.chord.length :=
          B.secondGapChordFinish_le j
        have hstartEq := B.secondGapChordStart_of_next_forward j e he hfwd
        have hne : B.secondGapChordStart j ≠ B.secondGapChordFinish j := by
          intro heq
          have hzero : (orientedSegment B.chord (B.secondGapChordStart j)
              (B.secondGapChordFinish j)).length = 0 := by
            rw [heq, orientedSegment, if_pos (le_refl _)]
            simp
          omega
        omega
      have hsegEq : orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j) =
          orientedSegment B.chord
            (B.brokenAssignment.second.partner
              (HalfEntry.entrySource B.brokenAssignment.index.second e) + 1)
            (B.secondGapChordFinish j) := by
        rw [B.secondGapChordStart_of_next_forward j e he hfwd]
      have hseg' : 0 < (orientedSegment B.chord
          (B.brokenAssignment.second.partner
            (HalfEntry.entrySource B.brokenAssignment.index.second e) + 1)
          (B.secondGapChordFinish j)).length := by
        rw [← hsegEq]
        exact hsegPos
      rw [List.getElem_of_eq hsegEq hsegPos] at hchordHead
      have hchordLetter :=
        (isCompOf_head_orientedSegment_succ_iff (P.label s) B.chord
          (y := B.brokenAssignment.second.partner
            (HalfEntry.entrySource B.brokenAssignment.index.second e))
          hfinishGe hy hseg').mp hchordHead
      have hmlt := B.secondChordPos_lt
        (B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second e) + 1) hy
      have hletterWord := (B.isCompOf_secondWord_chordPos_iff (P.label s)
        (B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second e) + 1) hy
        hmlt).mpr hchordLetter
      have hsucc := B.secondChordPos_succ
        (B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second e))
      have hconn0 : (B.secondBrokenConnectors
          (HalfEntry.entrySource B.brokenAssignment.index.second e)
          htBroken).startThroughPartner = [] := by
        have hlen : ((B.secondBrokenConnectors
            (HalfEntry.entrySource B.brokenAssignment.index.second e)
            htBroken).startThroughPartner).length = 0 := by
          rw [← B.secondGapRight_of_next_forward j e he hfwd]
          exact hright0
        exact List.length_eq_zero_iff.mp hlen
      have hvalue := ComponentConnectorPair.startThroughPartner_value
        (B.secondBrokenConnectors
          (HalfEntry.entrySource B.brokenAssignment.index.second e) htBroken)
      rw [hconn0, RelLetter.listVal_nil] at hvalue
      have hpartnerEnd := B.secondBrokenConnectors_partnerEnd
        (HalfEntry.entrySource B.brokenAssignment.index.second e) htBroken
      have hvertT : vertex B.secondBase B.secondWord
          (B.secondTargetPos (HalfEntry.entrySource
            B.brokenAssignment.index.second e)) =
          vertex B.secondBase B.secondWord
            ((B.secondBrokenConnectors
              (HalfEntry.entrySource B.brokenAssignment.index.second e)
              htBroken).partnerEnd) :=
        inv_mul_eq_one.mp hvalue.symm
      have hvert : vertex B.secondBase B.secondWord (B.secondTargetPos s + 1) =
          vertex B.secondBase B.secondWord (B.secondChordPos
            (B.brokenAssignment.second.partner
              (HalfEntry.entrySource
                B.brokenAssignment.index.second e) + 1)) := by
        rw [hadj, hsucc, ← hpartnerEnd]
        exact hvertT
      have hposM : B.secondArcLength ≤ B.secondChordPos
          (B.brokenAssignment.second.partner
            (HalfEntry.entrySource
              B.brokenAssignment.index.second e) + 1) := by
        simp only [secondChordPos]
        omega
      exact B.secondSurvivor_not_isCompOf_of_vertex_eq s hsurv _ _ hmlt
        (le_of_lt hmlt) (le_refl _) (by omega) (by omega) hvert hletterWord
    · obtain ⟨p, hp'⟩ := Option.ne_none_iff_exists'.mp
        (B.secondGapRunsForward_prev_isSome j hfwd)
      have hp : HalfGap.previousEntry B.brokenAssignment.index.second j =
          some p := by simpa using hp'
      have hnotlt : ¬ (B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second e) <
          B.brokenAssignment.second.partner
            (HalfEntry.entrySource B.brokenAssignment.index.second p)) := by
        intro hlt
        exact hfwd ((B.secondGapRunsForward_iff_of_adjacent j p e hp he).mpr hlt)
      have hpBroken := HalfEntry.entrySource_mem
        B.brokenAssignment.index.second p
      have hpartnerNe : B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second p) ≠
          B.brokenAssignment.second.partner
            (HalfEntry.entrySource B.brokenAssignment.index.second e) := by
        intro hEq
        exact HalfGap.entrySource_ne_of_adjacent
          B.brokenAssignment.index.second j hp he
          (B.brokenAssignment.second.partner_injective hpBroken htBroken hEq)
      have hfinishLe : B.secondGapChordFinish j ≤
          B.brokenAssignment.second.partner
            (HalfEntry.entrySource B.brokenAssignment.index.second e) := by
        rw [B.secondGapChordFinish_of_prev_backward j p hp hfwd]
        omega
      have hstartEq := B.secondGapChordStart_of_next_backward j e he hfwd
      have hpt : 0 < B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second e) := by
        by_contra hcon
        have h0 : B.brokenAssignment.second.partner
            (HalfEntry.entrySource
              B.brokenAssignment.index.second e) = 0 := by omega
        have hcf0 : B.secondGapChordFinish j = 0 := by omega
        have hzero : (orientedSegment B.chord (B.secondGapChordStart j)
            (B.secondGapChordFinish j)).length = 0 := by
          rw [hstartEq, h0, hcf0, orientedSegment, if_pos (le_refl 0)]
          simp
        omega
      have hsegEq : orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j) =
          orientedSegment B.chord
            (B.brokenAssignment.second.partner
              (HalfEntry.entrySource B.brokenAssignment.index.second e))
            (B.secondGapChordFinish j) := by
        rw [hstartEq]
      have hseg' : 0 < (orientedSegment B.chord
          (B.brokenAssignment.second.partner
            (HalfEntry.entrySource B.brokenAssignment.index.second e))
          (B.secondGapChordFinish j)).length := by
        rw [← hsegEq]
        exact hsegPos
      rw [List.getElem_of_eq hsegEq hsegPos] at hchordHead
      have hy1 : B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second e) - 1 <
          B.chord.length := by omega
      have hchordLetter :=
        (isCompOf_head_orientedSegment_pred_iff (P.label s) B.chord
          hfinishLe (by omega) hy1 hseg').mp hchordHead
      have hmlt := B.secondChordPos_lt
        (B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second e) - 1) hy1
      have hletterWord := (B.isCompOf_secondWord_chordPos_iff (P.label s)
        (B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second e) - 1) hy1
        hmlt).mpr hchordLetter
      have hsucc := B.secondChordPos_succ
        (B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second e) - 1)
      have hshift : B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second e) - 1 + 1 =
          B.brokenAssignment.second.partner
            (HalfEntry.entrySource
              B.brokenAssignment.index.second e) := by omega
      have hconn0 : (B.secondBrokenConnectors
          (HalfEntry.entrySource B.brokenAssignment.index.second e)
          htBroken).startConnector = [] := by
        have hlen : ((B.secondBrokenConnectors
            (HalfEntry.entrySource B.brokenAssignment.index.second e)
            htBroken).startConnector).length = 0 := by
          rw [← B.secondGapRight_of_next_backward j e he hfwd]
          exact hright0
        exact List.length_eq_zero_iff.mp hlen
      have hvalue := (B.secondBrokenConnectors
        (HalfEntry.entrySource B.brokenAssignment.index.second e)
        htBroken).start_value
      rw [hconn0, RelLetter.listVal_nil] at hvalue
      have hvertT : vertex B.secondBase B.secondWord
          (B.secondTargetPos (HalfEntry.entrySource
            B.brokenAssignment.index.second e)) =
          vertex B.secondBase B.secondWord (B.secondChordPos
            (B.brokenAssignment.second.partner
              (HalfEntry.entrySource B.brokenAssignment.index.second e))) :=
        inv_mul_eq_one.mp hvalue.symm
      have hvert : vertex B.secondBase B.secondWord (B.secondTargetPos s + 1) =
          vertex B.secondBase B.secondWord (B.secondChordPos
            (B.brokenAssignment.second.partner
              (HalfEntry.entrySource
                B.brokenAssignment.index.second e) - 1) + 1) := by
        rw [hadj, ← hsucc, hshift]
        exact hvertT
      have hposM : B.secondArcLength ≤ B.secondChordPos
          (B.brokenAssignment.second.partner
            (HalfEntry.entrySource
              B.brokenAssignment.index.second e) - 1) := by
        simp only [secondChordPos]
        omega
      have hzle : B.secondChordPos
          (B.brokenAssignment.second.partner
            (HalfEntry.entrySource B.brokenAssignment.index.second e) - 1)
          + 1 ≤ B.secondWord.length := by
        have hlt2 := B.secondChordPos_lt
          (B.brokenAssignment.second.partner
            (HalfEntry.entrySource B.brokenAssignment.index.second e))
          hpartnerLt
        have hval : B.secondChordPos
            (B.brokenAssignment.second.partner
              (HalfEntry.entrySource B.brokenAssignment.index.second e) - 1)
            + 1 = B.secondChordPos
              (B.brokenAssignment.second.partner
                (HalfEntry.entrySource
                  B.brokenAssignment.index.second e)) := by
          rw [← hsucc, hshift]
        omega
      exact B.secondSurvivor_not_isCompOf_of_vertex_eq s hsurv _ _ hmlt hzle
        (by omega) (by omega) (by omega) hvert hletterWord

/-! ## The inherited-arc component field, unconditionally -/

/-- The `arcComponent` field of `FirstGapComponentFamily`, with no residual
hypothesis. -/
theorem firstGapArcComponentField
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j) :
    IsComp (B.firstGapLocalLabel j
        ((B.firstGapLeft j).length +
          (B.firstTargetSide s - B.firstGapStartSide j)))
      (B.firstGapCycle j)
      (B.firstGapCut j ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j)))
      (B.firstGapCut j ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j) + 1)) :=
  B.firstGapArcSource_fullComponent_of_chordSeam j s hs
    (B.firstGapArcChordSeam_of_source j s hs)

/-- The `arcComponent` field of `SecondGapComponentFamily`, with no residual
hypothesis. -/
theorem secondGapArcComponentField
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j) :
    IsComp (B.secondGapLocalLabel j
        ((B.secondGapLeft j).length +
          (B.secondTargetSide s - B.secondGapStartSide j)))
      (B.secondGapCycle j)
      (B.secondGapCut j ((B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j)))
      (B.secondGapCut j ((B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j) + 1)) :=
  B.secondGapArcSource_fullComponent_of_chordSeam j s hs
    (B.secondGapArcChordSeam_of_source j s hs)

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
