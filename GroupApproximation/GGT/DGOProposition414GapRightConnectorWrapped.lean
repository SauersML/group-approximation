import GroupApproximation.GGT.DGOProposition414GapRightConnector

/-!
# The right connector of a wrapped Proposition 4.14 gap child

Wrapped counterpart of `DGOProposition414GapRightConnector`.  The wrapped
half traverses the chord with the opposite default orientation, so the
boundary children take the other branch of `secondGapRunsForward`; everything
else is the mirror of the first-half argument, and the outcome is the same:
the `rightComponent` field of `SecondGapComponentFamily` holds outright.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-! ## Resolving the orientation branch of a wrapped gap -/

/-- A wrapped gap with no preceding broken entry traverses the chord
forwards. -/
theorem secondGapRunsForward_of_prev_none
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.second j = none) :
    B.secondGapRunsForward j := by
  simp only [secondGapRunsForward, hp]

/-- A backward wrapped gap has a preceding broken entry. -/
theorem secondGapRunsForward_prev_isSome
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (hfwd : ¬ B.secondGapRunsForward j) :
    HalfGap.previousEntry B.brokenAssignment.index.second j ≠ none := by
  intro hnone
  exact hfwd (B.secondGapRunsForward_of_prev_none j hnone)

/-- The orientation flag of an interior wrapped gap compares the two adjacent
chord partners. -/
theorem secondGapRunsForward_iff_of_adjacent
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (p e : Fin B.brokenAssignment.index.second.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.second j = some p)
    (he : HalfGap.nextEntry B.brokenAssignment.index.second j = some e) :
    B.secondGapRunsForward j ↔
      B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second e) <
        B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second p) := by
  simp only [secondGapRunsForward, hp, he]

/-- A forward wrapped gap leaves the chord at the far end of the next partner
edge. -/
theorem secondGapChordStart_of_next_forward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.second j = some e)
    (hfwd : B.secondGapRunsForward j) :
    B.secondGapChordStart j =
      B.brokenAssignment.second.partner
        (HalfEntry.entrySource B.brokenAssignment.index.second e) + 1 := by
  classical
  simp only [secondGapChordStart]
  rw [he]
  simp [hfwd]

/-- A backward wrapped gap leaves the chord at the near end of the next
partner edge. -/
theorem secondGapChordStart_of_next_backward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.second j = some e)
    (hfwd : ¬ B.secondGapRunsForward j) :
    B.secondGapChordStart j =
      B.brokenAssignment.second.partner
        (HalfEntry.entrySource B.brokenAssignment.index.second e) := by
  classical
  simp only [secondGapChordStart]
  rw [he]
  simp [hfwd]

/-- The initial wrapped gap reaches the terminal chord endpoint. -/
theorem secondGapChordFinish_of_prev_none
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.second j = none) :
    B.secondGapChordFinish j = B.chord.length := by
  classical
  simp only [secondGapChordFinish]
  rw [hp]

/-- A forward interior wrapped gap reaches the near end of the previous
partner edge. -/
theorem secondGapChordFinish_of_prev_forward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (p : Fin B.brokenAssignment.index.second.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.second j = some p)
    (hfwd : B.secondGapRunsForward j) :
    B.secondGapChordFinish j =
      B.brokenAssignment.second.partner
        (HalfEntry.entrySource B.brokenAssignment.index.second p) := by
  classical
  simp only [secondGapChordFinish]
  rw [hp]
  simp [hfwd]

/-- A backward interior wrapped gap reaches the far end of the previous
partner edge. -/
theorem secondGapChordFinish_of_prev_backward
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (p : Fin B.brokenAssignment.index.second.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.second j = some p)
    (hfwd : ¬ B.secondGapRunsForward j) :
    B.secondGapChordFinish j =
      B.brokenAssignment.second.partner
        (HalfEntry.entrySource B.brokenAssignment.index.second p) + 1 := by
  classical
  simp only [secondGapChordFinish]
  rw [hp]
  simp [hfwd]

/-! ## The wrapped chord head -/

/-- The first letter of the oriented child chord of a wrapped gap with a
following broken entry does not carry that entry's peripheral label. -/
theorem secondGap_chordHead_not_isCompOf_nextEntry
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.second j = some e)
    (hseg : 0 < (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)).length) :
    ¬ ((orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j))[0]'hseg).IsCompOf
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.second e)) := by
  classical
  intro hletter
  have htBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.second e
  have hcomp := B.secondPartner_chord_isComp
    (HalfEntry.entrySource B.brokenAssignment.index.second e) htBroken
  have hylt : B.brokenAssignment.second.partner
      (HalfEntry.entrySource B.brokenAssignment.index.second e) <
      B.chord.length :=
    B.brokenAssignment.second.partner_lt _ htBroken
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
      exact hseg
    rw [List.getElem_of_eq hsegEq hseg] at hletter
    exact not_isCompOf_head_orientedSegment_succ _ B.chord hcomp hfinishGe
      hseg' hletter
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
    have hsegEq : orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j) =
        orientedSegment B.chord
          (B.brokenAssignment.second.partner
            (HalfEntry.entrySource B.brokenAssignment.index.second e))
          (B.secondGapChordFinish j) := by
      rw [B.secondGapChordStart_of_next_backward j e he hfwd]
    have hseg' : 0 < (orientedSegment B.chord
        (B.brokenAssignment.second.partner
          (HalfEntry.entrySource B.brokenAssignment.index.second e))
        (B.secondGapChordFinish j)).length := by
      rw [← hsegEq]
      exact hseg
    rw [List.getElem_of_eq hsegEq hseg] at hletter
    exact not_isCompOf_head_orientedSegment_pred _ B.chord hcomp hfinishLe
      hseg' hletter

/-! ## Consecutive wrapped parent components carry different labels -/

/-- Wrapped counterpart of `firstTarget_label_ne_of_succ`. -/
theorem secondTarget_label_ne_of_succ
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    {s t : ℕ} (hs : s ∈ B.secondTarget) (ht : t ∈ B.secondTarget)
    (hadj : B.secondTargetPos s + 1 = B.secondTargetPos t) :
    P.label s ≠ P.label t := by
  have hltT : B.secondTargetPos t < B.secondArc.length := by
    have hend := (B.secondArc_targetComponent ht).2.1
    omega
  have hltS : B.secondTargetPos s + 1 < B.secondArc.length := by omega
  intro hEqLabel
  have hletterT := (B.secondArc_targetComponent ht).2.2.1
    (B.secondTargetPos t) le_rfl (by omega) hltT
  have hgoal : (B.secondArc[B.secondTargetPos s + 1]'hltS).IsCompOf
      (P.label s) := by
    rw [getElem_congr_idx hadj, hEqLabel]
    exact hletterT
  exact (B.secondArc_targetComponent hs).2.2.2.2 hltS hgoal

/-! ## The two neighbours of a wrapped right connector -/

/-- The letter preceding a wrapped right connector does not carry that
connector's label. -/
theorem secondGap_rightConnector_prev_exclusion
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.second j = some e)
    (hzero : 0 < (B.secondGapRight j).length) :
    ∀ q : ℕ,
      (B.secondGapLeft j).length +
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)).length = q + 1 →
      ∀ hq : q < (B.secondGapCycle j).length,
      ¬ ((B.secondGapCycle j)[q]'hq).IsCompOf
        (B.secondGapLocalLabel j ((B.secondGapLeft j).length +
          (B.secondGapFinishSide j - B.secondGapStartSide j))) := by
  classical
  intro q hq0 hq hletter
  have hlab : B.secondGapLocalLabel j ((B.secondGapLeft j).length +
      (B.secondGapFinishSide j - B.secondGapStartSide j)) =
      P.label (HalfEntry.entrySource B.brokenAssignment.index.second e) := by
    simpa using B.secondGapLocalLabel_rightConnector j e he 0 hzero
  rw [hlab] at hletter
  by_cases harc : 0 < (arcWord B.secondArc B.secondArcCut
      (B.secondGapStartSide j) (B.secondGapFinishSide j)).length
  · have hidx : q = (B.secondGapLeft j).length +
        ((arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length - 1) := by omega
    have hcycleLt : (B.secondGapLeft j).length +
        ((arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length - 1) <
        (B.secondGapCycle j).length := by omega
    have hgetEq : (B.secondGapCycle j)[q]'hq =
        (B.secondGapCycle j)[(B.secondGapLeft j).length +
          ((arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)).length - 1)]'hcycleLt :=
      getElem_congr_idx hidx
    rw [hgetEq] at hletter
    have hArcLt : (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)).length - 1 <
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length := by omega
    have hco := (isCompOf_auxiliaryCycle_arc_iff
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.second e))
      (B.secondGapLeft j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)) (B.secondGapRight j)
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j))
      ((arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)).length - 1) hArcLt hcycleLt).mp hletter
    exact B.secondGap_arcLast_not_isCompOf j e he harc
      (by simpa [List.get_eq_getElem] using hco)
  · have hqL : q < (B.secondGapLeft j).length := by omega
    have hprevNe : HalfGap.previousEntry B.brokenAssignment.index.second j
        ≠ none := by
      intro hnone
      have h0 : (B.secondGapLeft j).length = 0 := by
        simp only [secondGapLeft]
        rw [hnone]
        simp
      omega
    obtain ⟨p, hp'⟩ := Option.ne_none_iff_exists'.mp hprevNe
    have hp : HalfGap.previousEntry B.brokenAssignment.index.second j =
        some p := by simpa using hp'
    have hconn := B.secondGap_leftConnector_isCompOf j p hp q hqL hq
    have hconnLabel := B.secondGapLocalLabel_leftConnector j p hp q hqL
    have hconn' : ((B.secondGapCycle j)[q]'hq).IsCompOf
        (P.label (HalfEntry.entrySource
          B.brokenAssignment.index.second p)) := by
      rw [← hconnLabel]
      exact hconn
    have hEqLabel : P.label (HalfEntry.entrySource
          B.brokenAssignment.index.second p) =
        P.label (HalfEntry.entrySource
          B.brokenAssignment.index.second e) :=
      eq_of_isCompOf_of_isCompOf hconn' hletter
    have hpBroken := HalfEntry.entrySource_mem
      B.brokenAssignment.index.second p
    have heBroken := HalfEntry.entrySource_mem
      B.brokenAssignment.index.second e
    have hpTarget := (mem_brokenSet_iff.mp hpBroken).1
    have heTarget := (mem_brokenSet_iff.mp heBroken).1
    have hstartSide : B.secondGapStartSide j =
        B.secondTargetSide (HalfEntry.entrySource
          B.brokenAssignment.index.second p) + 1 := by
      simp only [secondGapStartSide]
      rw [hp]
    have hfinishSide : B.secondGapFinishSide j =
        B.secondTargetSide (HalfEntry.entrySource
          B.brokenAssignment.index.second e) := by
      simp only [secondGapFinishSide]
      rw [he]
    have hcutEnd : B.secondArcCut (B.secondGapFinishSide j) ≤
        B.secondArc.length :=
      B.secondArc_isCutPath.cut.le_length (B.secondGapFinishSide_le j)
    have harcLen : (arcWord B.secondArc B.secondArcCut
        (B.secondGapStartSide j) (B.secondGapFinishSide j)).length =
        B.secondArcCut (B.secondGapFinishSide j) -
          B.secondArcCut (B.secondGapStartSide j) :=
      length_arcWord B.secondArc B.secondArcCut hcutEnd
    have hcutStart : B.secondArcCut (B.secondGapStartSide j) =
        B.secondTargetPos (HalfEntry.entrySource
          B.brokenAssignment.index.second p) + 1 := by
      rw [hstartSide]
      exact (B.secondArcCut_target hpTarget).2
    have hcutFinish : B.secondArcCut (B.secondGapFinishSide j) =
        B.secondTargetPos (HalfEntry.entrySource
          B.brokenAssignment.index.second e) := by
      rw [hfinishSide]
      exact (B.secondArcCut_target heTarget).1
    have hposLt : B.secondTargetPos (HalfEntry.entrySource
          B.brokenAssignment.index.second p) <
        B.secondTargetPos (HalfEntry.entrySource
          B.brokenAssignment.index.second e) :=
      HalfGap.pos_entrySource_lt_of_adjacent
        B.brokenAssignment.index.second j hp he
    have hadj : B.secondTargetPos (HalfEntry.entrySource
          B.brokenAssignment.index.second p) + 1 =
        B.secondTargetPos (HalfEntry.entrySource
          B.brokenAssignment.index.second e) := by omega
    exact B.secondTarget_label_ne_of_succ hpTarget heTarget hadj hEqLabel

/-- The letter following a wrapped right connector does not carry that
connector's label. -/
theorem secondGap_rightConnector_next_exclusion
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.second j = some e)
    (hzero : 0 < (B.secondGapRight j).length) :
    ∀ hn : (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length + 1 <
        (B.secondGapCycle j).length,
      ¬ ((B.secondGapCycle j).get ⟨
        (B.secondGapLeft j).length +
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)).length + 1, hn⟩).IsCompOf
        (B.secondGapLocalLabel j ((B.secondGapLeft j).length +
          (B.secondGapFinishSide j - B.secondGapStartSide j))) := by
  classical
  intro hn hletter
  have hlab : B.secondGapLocalLabel j ((B.secondGapLeft j).length +
      (B.secondGapFinishSide j - B.secondGapStartSide j)) =
      P.label (HalfEntry.entrySource B.brokenAssignment.index.second e) := by
    simpa using B.secondGapLocalLabel_rightConnector j e he 0 hzero
  rw [hlab] at hletter
  have hone : (B.secondGapRight j).length = 1 := by
    have hle := B.secondGapRight_length_le_one j
    omega
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
      (B.secondGapRight j).length + 0 < (B.secondGapCycle j).length := by omega
  have hgetEq : (B.secondGapCycle j)[(B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length + 1]'hn =
      (B.secondGapCycle j)[(B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length + 0]'hn' :=
    getElem_congr_idx (by omega)
  rw [List.get_eq_getElem, hgetEq] at hletter
  have hchord := (isCompOf_auxiliaryCycle_chord_iff
    (P.label (HalfEntry.entrySource B.brokenAssignment.index.second e))
    (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)) (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)) 0 hsegPos hn').mp hletter
  exact B.secondGap_chordHead_not_isCompOf_nextEntry j e he hsegPos hchord

/-! ## The wrapped right connector component, unconditionally -/

/-- A wrapped right connector is a maximal one-letter component of its
auxiliary cycle. -/
theorem secondGap_rightConnector_component
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.second j = some e)
    (hzero : 0 < (B.secondGapRight j).length) :
    IsComp (B.secondGapLocalLabel j ((B.secondGapLeft j).length +
        (B.secondGapFinishSide j - B.secondGapStartSide j)))
      (B.secondGapCycle j)
      (B.secondGapCut j ((B.secondGapLeft j).length +
        (B.secondGapFinishSide j - B.secondGapStartSide j)))
      (B.secondGapCut j ((B.secondGapLeft j).length +
        (B.secondGapFinishSide j - B.secondGapStartSide j) + 1)) :=
  B.secondGap_rightConnector_cycleComponent j e he hzero
    (B.secondGap_rightConnector_prev_exclusion j e he hzero)
    (B.secondGap_rightConnector_next_exclusion j e he hzero)

/-- The `rightComponent` field of `SecondGapComponentFamily`, with no residual
hypothesis. -/
theorem secondGap_rightComponent
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (r : ℕ) (hr : r < (B.secondGapRight j).length) :
    IsComp (B.secondGapLocalLabel j ((B.secondGapLeft j).length +
        (B.secondGapFinishSide j - B.secondGapStartSide j) + r))
      (B.secondGapCycle j)
      (B.secondGapCut j ((B.secondGapLeft j).length +
        (B.secondGapFinishSide j - B.secondGapStartSide j) + r))
      (B.secondGapCut j ((B.secondGapLeft j).length +
        (B.secondGapFinishSide j - B.secondGapStartSide j) + r + 1)) := by
  classical
  have hle := B.secondGapRight_length_le_one j
  have hr0 : r = 0 := by omega
  subst hr0
  have hzero : 0 < (B.secondGapRight j).length := by omega
  have hnxt : HalfGap.nextEntry B.brokenAssignment.index.second j ≠ none := by
    intro hnone
    have h0 : (B.secondGapRight j).length = 0 := by
      simp only [secondGapRight]
      rw [hnone]
      simp
    omega
  obtain ⟨e, he'⟩ := Option.ne_none_iff_exists'.mp hnxt
  have he : HalfGap.nextEntry B.brokenAssignment.index.second j = some e := by
    simpa using he'
  simpa using B.secondGap_rightConnector_component j e he hzero

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
