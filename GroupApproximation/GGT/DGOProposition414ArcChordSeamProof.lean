import GroupApproximation.GGT.DGOProposition414HalfWordChord

/-!
# The degenerate arc/chord seam of a Proposition 4.14 gap child

The last case of the inherited-arc maximality clause is the one where the gap
arc ends at a broken source `p_{i_j}` whose connector `f_j` degenerates to the
empty path, so that the auxiliary cycle passes straight from the retained
source `p_i` into the child chord.  Dahmani--Guirardel--Osin exclude a
same-label chord letter there with

> a path `p_i \in I_1 \setminus J_1` can not be connected to a component of `t`
> according to our choice of `p_{i_1}, \ldots , p_{i_l}`

(arXiv:1111.7048, proof of Proposition 4.14).  Formally: an empty connector
makes the terminal vertex of `p_i` a vertex of the chord block of the half
word, so a same-label chord letter there lies in a run of the half word whose
start is connected to `p_i`, contradicting the isolation clause carried by a
surviving source.  This closes `FirstGapArcChordSeam` outright.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-! ## Isolation of a surviving source, in the form the seams consume -/

/-- A surviving first-half source meets no same-label letter of the half word
whose run reaches a vertex its own component reaches.  The vertex hypothesis
is what an empty connector supplies. -/
theorem firstSurvivor_not_isCompOf_of_vertex_eq
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hsurv : B.componentPlacement.firstSurvives s)
    (m z : ℕ) (hmlt : m < B.firstWord.length)
    (hzle : z ≤ B.firstWord.length) (hmz : m ≤ z) (hzm : z ≤ m + 1)
    (hpos : B.firstTargetPos s < m)
    (hvert : vertex B.firstBase B.firstWord (B.firstTargetPos s + 1) =
      vertex B.firstBase B.firstWord z) :
    ¬ (B.firstWord[m]'hmlt).IsCompOf (P.label s) := by
  intro hletter
  have hcompS : IsComp (P.label s) B.firstWord (B.firstTargetPos s)
      (B.firstTargetPos s + 1) := hsurv.1
  have hisoS : IsIsolated D.fam (P.label s) B.firstBase B.firstWord
      (B.firstTargetPos s) := hsurv.2
  obtain ⟨a, bb, ha, hb, hcomp⟩ :=
    exists_isComp_of_isCompOf (P.label s) B.firstWord m hmlt hletter
  have hspan : (vertex B.firstBase B.firstWord a)⁻¹ *
      vertex B.firstBase B.firstWord z ∈ D.fam (P.label s) :=
    span_mem_fam D (P.label s) B.firstBase B.firstWord_letters z hzle a
      (by omega) (fun q hq1 hq2 hq => hcomp.2.2.1 q hq1 (by omega) hq)
  have hspanS : (vertex B.firstBase B.firstWord (B.firstTargetPos s))⁻¹ *
      vertex B.firstBase B.firstWord (B.firstTargetPos s + 1) ∈
      D.fam (P.label s) :=
    span_mem_fam_of_isComp D B.firstBase B.firstWord_letters hcompS
  have hconn : Connected D.fam (P.label s) B.firstBase B.firstWord
      (B.firstTargetPos s) a := by
    show (vertex B.firstBase B.firstWord (B.firstTargetPos s))⁻¹ *
      vertex B.firstBase B.firstWord a ∈ D.fam (P.label s)
    have hfac : (vertex B.firstBase B.firstWord (B.firstTargetPos s))⁻¹ *
        vertex B.firstBase B.firstWord a =
        ((vertex B.firstBase B.firstWord (B.firstTargetPos s))⁻¹ *
            vertex B.firstBase B.firstWord (B.firstTargetPos s + 1)) *
          ((vertex B.firstBase B.firstWord a)⁻¹ *
            vertex B.firstBase B.firstWord z)⁻¹ := by
      rw [hvert]
      group
    rw [hfac]
    exact mul_mem hspanS (inv_mem hspan)
  have hane : a ≠ B.firstTargetPos s := by
    intro heq
    have hlt : B.firstTargetPos s + 1 < B.firstWord.length := by omega
    have hin : (B.firstWord[B.firstTargetPos s + 1]'hlt).IsCompOf
        (P.label s) :=
      hcomp.2.2.1 (B.firstTargetPos s + 1) (by omega) (by omega) hlt
    exact hcompS.2.2.2.2 hlt hin
  exact hisoS.2 a hane ⟨bb, hcomp⟩ hconn

/-! ## Which connector a first-half gap actually carries -/

/-- A forward first-half gap carries the start connector of its following
broken source. -/
theorem firstGapRight_of_next_forward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.first j = some e)
    (hfwd : B.firstGapRunsForward j) :
    B.firstGapRight j =
      (B.firstBrokenConnectors
        (HalfEntry.entrySource B.brokenAssignment.index.first e)
        (HalfEntry.entrySource_mem
          B.brokenAssignment.index.first e)).startConnector := by
  classical
  simp only [firstGapRight]
  rw [he]
  simp [hfwd]

/-- A backward first-half gap carries the compressed through-partner connector
of its following broken source. -/
theorem firstGapRight_of_next_backward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.first j = some e)
    (hfwd : ¬ B.firstGapRunsForward j) :
    B.firstGapRight j =
      (B.firstBrokenConnectors
        (HalfEntry.entrySource B.brokenAssignment.index.first e)
        (HalfEntry.entrySource_mem
          B.brokenAssignment.index.first e)).startThroughPartner := by
  classical
  simp only [firstGapRight]
  rw [he]
  simp [hfwd]

/-! ## The gap arc ends at the next broken source -/

/-- When the inherited arc of a gap ends at its retained target, the following
broken source is the very next parent component. -/
theorem firstGapArcSource_terminal_pos_succ
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.first j = some e)
    (hterminal :
      B.firstArcCut (B.firstTargetSide s) -
          B.firstArcCut (B.firstGapStartSide j) + 1 =
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length) :
    B.firstTargetPos s + 1 =
      B.firstTargetPos (HalfEntry.entrySource
        B.brokenAssignment.index.first e) := by
  have hsData := Finset.mem_filter.mp hs
  have htBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
  have htTarget := (mem_brokenSet_iff.mp htBroken).1
  have hcutEnd : B.firstArcCut (B.firstGapFinishSide j) ≤ B.firstArc.length :=
    B.firstArc_isCutPath.cut.le_length (B.firstGapFinishSide_le j)
  have harcLen : (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)).length =
      B.firstArcCut (B.firstGapFinishSide j) -
        B.firstArcCut (B.firstGapStartSide j) :=
    length_arcWord B.firstArc B.firstArcCut hcutEnd
  have hfinishSide : B.firstGapFinishSide j =
      B.firstTargetSide (HalfEntry.entrySource
        B.brokenAssignment.index.first e) := by
    simp only [firstGapFinishSide]
    rw [he]
  have hposT : B.firstArcCut (B.firstGapFinishSide j) =
      B.firstTargetPos (HalfEntry.entrySource
        B.brokenAssignment.index.first e) := by
    rw [hfinishSide, (B.firstArcCut_target htTarget).1]
  have hposS : B.firstArcCut (B.firstTargetSide s) = B.firstTargetPos s :=
    (B.firstArcCut_target hsData.1).1
  have hstartLe : B.firstArcCut (B.firstGapStartSide j) ≤
      B.firstArcCut (B.firstTargetSide s) :=
    B.firstArc_isCutPath.cut.mono_le hsData.2.1
  rw [← hposS, ← hposT]
  omega

/-! ## The seam, closed -/

/-- The residual chord seam of the inherited-arc maximality clause holds
outright: the letter after a retained arc target never carries its label. -/
theorem firstGapArcChordSeam_of_source
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j) :
    FirstGapArcChordSeam B j s := by
  classical
  by_cases hnone : HalfGap.nextEntry B.brokenAssignment.index.first j = none
  · exact firstGapArcChordSeam_of_lastGap B j s hs hnone
  · obtain ⟨e, he'⟩ := Option.ne_none_iff_exists'.mp hnone
    have he : HalfGap.nextEntry B.brokenAssignment.index.first j =
        some e := by simpa using he'
    intro hright0 hterminal hn hletter
    have hsData := Finset.mem_filter.mp hs
    have htBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
    have hsurv := B.firstGapArcSource_survives j s hs
    have hadj := B.firstGapArcSource_terminal_pos_succ j s hs e he hterminal
    have hpartnerLt : B.brokenAssignment.first.partner
        (HalfEntry.entrySource B.brokenAssignment.index.first e) <
        B.chord.length :=
      B.brokenAssignment.first.partner_lt _ htBroken
    have hposSlt : B.firstTargetPos s < B.firstArcLength :=
      B.firstTargetPos_lt hsData.1
    -- the terminal cycle letter is the head of the child chord
    have hcycleLen : (B.firstGapCycle j).length =
        (B.firstGapLeft j).length +
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)).length +
          (B.firstGapRight j).length +
          (orientedSegment B.chord (B.firstGapChordStart j)
            (B.firstGapChordFinish j)).length := by
      simp only [firstGapCycle, auxiliaryCycleWord, List.length_append,
        OsinComponents.length_revWord]
    have hsegPos : 0 < (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j)).length := by omega
    have hn' : (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length + 0 < (B.firstGapCycle j).length := by omega
    have hgetEq : (B.firstGapCycle j)[(B.firstGapLeft j).length +
          (B.firstArcCut (B.firstTargetSide s) -
            B.firstArcCut (B.firstGapStartSide j)) + 1]'hn =
        (B.firstGapCycle j)[(B.firstGapLeft j).length +
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)).length +
          (B.firstGapRight j).length + 0]'hn' :=
      getElem_congr_idx (by omega)
    rw [hgetEq] at hletter
    have hchordHead := (isCompOf_auxiliaryCycle_chord_iff (P.label s)
      (B.firstGapLeft j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)) (B.firstGapRight j)
      (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j)) 0 hsegPos hn').mp hletter
    by_cases hfwd : B.firstGapRunsForward j
    · -- the child chord runs forwards from just past the partner edge
      obtain ⟨p, hp'⟩ := Option.ne_none_iff_exists'.mp
        (B.firstGapRunsForward_previousEntry_isSome j hfwd)
      have hp : HalfGap.previousEntry B.brokenAssignment.index.first j =
          some p := by simpa using hp'
      have hlt := (B.firstGapRunsForward_iff_of_adjacent j p e hp he).mp hfwd
      have hpartnerPlt : B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first p) <
          B.chord.length :=
        B.brokenAssignment.first.partner_lt _
          (HalfEntry.entrySource_mem B.brokenAssignment.index.first p)
      have hy : B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first e) + 1 <
          B.chord.length := by omega
      have hsegEq : orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j) =
          orientedSegment B.chord
            (B.brokenAssignment.first.partner
              (HalfEntry.entrySource B.brokenAssignment.index.first e) + 1)
            (B.brokenAssignment.first.partner
              (HalfEntry.entrySource
                B.brokenAssignment.index.first p)) := by
        rw [B.firstGapChordStart_of_next_forward j e he hfwd,
          B.firstGapChordFinish_of_prev_forward j p hp hfwd]
      have hseg' : 0 < (orientedSegment B.chord
          (B.brokenAssignment.first.partner
            (HalfEntry.entrySource B.brokenAssignment.index.first e) + 1)
          (B.brokenAssignment.first.partner
            (HalfEntry.entrySource
              B.brokenAssignment.index.first p))).length := by
        rw [← hsegEq]
        exact hsegPos
      rw [List.getElem_of_eq hsegEq hsegPos] at hchordHead
      have hchordLetter :=
        (isCompOf_head_orientedSegment_succ_iff (P.label s) B.chord
          (y := B.brokenAssignment.first.partner
            (HalfEntry.entrySource B.brokenAssignment.index.first e))
          (by omega) hy hseg').mp hchordHead
      have hmlt := B.firstChordPos_lt
        (B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first e) + 1) hy
      have hletterWord := (B.isCompOf_firstWord_chordPos_iff (P.label s)
        (B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first e) + 1) hy
        hmlt).mpr hchordLetter
      have hsucc := B.firstChordPos_succ
        (B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first e)) hy
      have hconn0 : (B.firstBrokenConnectors
          (HalfEntry.entrySource B.brokenAssignment.index.first e)
          htBroken).startConnector = [] := by
        have hlen : ((B.firstBrokenConnectors
            (HalfEntry.entrySource B.brokenAssignment.index.first e)
            htBroken).startConnector).length = 0 := by
          rw [← B.firstGapRight_of_next_forward j e he hfwd]
          exact hright0
        exact List.length_eq_zero_iff.mp hlen
      have hvalue := (B.firstBrokenConnectors
        (HalfEntry.entrySource B.brokenAssignment.index.first e)
        htBroken).start_value
      rw [hconn0, RelLetter.listVal_nil] at hvalue
      have hvertT : vertex B.firstBase B.firstWord
          (B.firstTargetPos (HalfEntry.entrySource
            B.brokenAssignment.index.first e)) =
          vertex B.firstBase B.firstWord (B.firstChordPos
            (B.brokenAssignment.first.partner
              (HalfEntry.entrySource B.brokenAssignment.index.first e))) :=
        inv_mul_eq_one.mp hvalue.symm
      have hvert : vertex B.firstBase B.firstWord (B.firstTargetPos s + 1) =
          vertex B.firstBase B.firstWord (B.firstChordPos
            (B.brokenAssignment.first.partner
              (HalfEntry.entrySource B.brokenAssignment.index.first e) + 1)
            + 1) := by
        rw [hadj, hsucc]
        exact hvertT
      have hposM : B.firstArcLength ≤ B.firstChordPos
          (B.brokenAssignment.first.partner
            (HalfEntry.entrySource B.brokenAssignment.index.first e) + 1) := by
        simp only [firstChordPos]
        omega
      have hzle : B.firstChordPos
          (B.brokenAssignment.first.partner
            (HalfEntry.entrySource B.brokenAssignment.index.first e) + 1)
          + 1 ≤ B.firstWord.length := by omega
      exact B.firstSurvivor_not_isCompOf_of_vertex_eq s hsurv _ _ hmlt hzle
        (by omega) (by omega) (by omega) hvert hletterWord
    · -- the child chord runs backwards from the near end of the partner edge
      have hfinishLe : B.firstGapChordFinish j ≤
          B.brokenAssignment.first.partner
            (HalfEntry.entrySource B.brokenAssignment.index.first e) := by
        cases hp : HalfGap.previousEntry B.brokenAssignment.index.first j with
        | none =>
            rw [B.firstGapChordFinish_of_prev_none j hp]
            exact Nat.zero_le _
        | some p =>
            have hnotlt : ¬ (B.brokenAssignment.first.partner
                (HalfEntry.entrySource B.brokenAssignment.index.first e) <
                B.brokenAssignment.first.partner
                  (HalfEntry.entrySource
                    B.brokenAssignment.index.first p)) := by
              intro hlt
              exact hfwd
                ((B.firstGapRunsForward_iff_of_adjacent j p e hp he).mpr hlt)
            have hpBroken := HalfEntry.entrySource_mem
              B.brokenAssignment.index.first p
            have hpartnerNe : B.brokenAssignment.first.partner
                (HalfEntry.entrySource B.brokenAssignment.index.first p) ≠
                B.brokenAssignment.first.partner
                  (HalfEntry.entrySource
                    B.brokenAssignment.index.first e) := by
              intro hEq
              exact HalfGap.entrySource_ne_of_adjacent
                B.brokenAssignment.index.first j hp he
                (B.brokenAssignment.first.partner_injective hpBroken htBroken
                  hEq)
            rw [B.firstGapChordFinish_of_prev_backward j p hp hfwd]
            omega
      have hstartEq := B.firstGapChordStart_of_next_backward j e he hfwd
      have hpt : 0 < B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first e) := by
        by_contra hcon
        have h0 : B.brokenAssignment.first.partner
            (HalfEntry.entrySource B.brokenAssignment.index.first e) = 0 := by
          omega
        have hcf0 : B.firstGapChordFinish j = 0 := by omega
        have hzero : (orientedSegment B.chord (B.firstGapChordStart j)
            (B.firstGapChordFinish j)).length = 0 := by
          rw [hstartEq, h0, hcf0, orientedSegment, if_pos (le_refl 0)]
          simp
        omega
      have hsegEq : orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j) =
          orientedSegment B.chord
            (B.brokenAssignment.first.partner
              (HalfEntry.entrySource B.brokenAssignment.index.first e))
            (B.firstGapChordFinish j) := by
        rw [hstartEq]
      have hseg' : 0 < (orientedSegment B.chord
          (B.brokenAssignment.first.partner
            (HalfEntry.entrySource B.brokenAssignment.index.first e))
          (B.firstGapChordFinish j)).length := by
        rw [← hsegEq]
        exact hsegPos
      rw [List.getElem_of_eq hsegEq hsegPos] at hchordHead
      have hy1 : B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first e) - 1 <
          B.chord.length := by omega
      have hchordLetter :=
        (isCompOf_head_orientedSegment_pred_iff (P.label s) B.chord
          hfinishLe (by omega) hy1 hseg').mp hchordHead
      have hmlt := B.firstChordPos_lt
        (B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first e) - 1) hy1
      have hletterWord := (B.isCompOf_firstWord_chordPos_iff (P.label s)
        (B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first e) - 1) hy1
        hmlt).mpr hchordLetter
      have hpred := B.firstChordPos_pred
        (B.brokenAssignment.first.partner
          (HalfEntry.entrySource B.brokenAssignment.index.first e)) hpt
        hpartnerLt
      have hconn0 : (B.firstBrokenConnectors
          (HalfEntry.entrySource B.brokenAssignment.index.first e)
          htBroken).startThroughPartner = [] := by
        have hlen : ((B.firstBrokenConnectors
            (HalfEntry.entrySource B.brokenAssignment.index.first e)
            htBroken).startThroughPartner).length = 0 := by
          rw [← B.firstGapRight_of_next_backward j e he hfwd]
          exact hright0
        exact List.length_eq_zero_iff.mp hlen
      have hvalue := ComponentConnectorPair.startThroughPartner_value
        (B.firstBrokenConnectors
          (HalfEntry.entrySource B.brokenAssignment.index.first e) htBroken)
      rw [hconn0, RelLetter.listVal_nil] at hvalue
      have hpartnerEnd := B.firstBrokenConnectors_partnerEnd
        (HalfEntry.entrySource B.brokenAssignment.index.first e) htBroken
      have hvertT : vertex B.firstBase B.firstWord
          (B.firstTargetPos (HalfEntry.entrySource
            B.brokenAssignment.index.first e)) =
          vertex B.firstBase B.firstWord
            ((B.firstBrokenConnectors
              (HalfEntry.entrySource B.brokenAssignment.index.first e)
              htBroken).partnerEnd) :=
        inv_mul_eq_one.mp hvalue.symm
      have hvert : vertex B.firstBase B.firstWord (B.firstTargetPos s + 1) =
          vertex B.firstBase B.firstWord (B.firstChordPos
            (B.brokenAssignment.first.partner
              (HalfEntry.entrySource
                B.brokenAssignment.index.first e) - 1)) := by
        rw [hadj, hpred, ← hpartnerEnd]
        exact hvertT
      have hposM : B.firstArcLength ≤ B.firstChordPos
          (B.brokenAssignment.first.partner
            (HalfEntry.entrySource B.brokenAssignment.index.first e) - 1) := by
        simp only [firstChordPos]
        omega
      exact B.firstSurvivor_not_isCompOf_of_vertex_eq s hsurv _ _ hmlt
        (le_of_lt hmlt) (le_refl _) (by omega) (by omega) hvert hletterWord

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
