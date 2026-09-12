import GroupApproximation.GGT.DGOProposition414GapChordHead

/-!
# The right connector of a Proposition 4.14 gap child is a component

In Dahmani--Guirardel--Osin's auxiliary cycle
`c_j = e_{j-1}^{-1} p_{i_{j-1}+1} … p_{i_j-1} f_j [(y_j)_-,(y_{j-1})_+]`
the connector `f_j` is a single peripheral letter labelled by the following
broken source `p_{i_j}`.  It is a maximal component of `c_j` once its two
neighbouring letters are excluded, and this file discharges both:

* the letter before `f_j` is the last inherited arc letter when the gap arc is
  nonempty, excluded by the landed `firstGap_arcLast_not_isCompOf`; when the
  gap arc is empty it is the preceding connector `e_{j-1}`, whose label is that
  of `p_{i_{j-1}}`, and the two broken sources are then consecutive one-edge
  components of the parent arc, so their labels differ;
* the letter after `f_j` is the head of the oriented child chord, excluded by
  `firstGap_chordHead_not_isCompOf_nextEntry`.

Together these give the `rightComponent` field of `FirstGapComponentFamily`
outright, with no residual hypothesis.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace HalfGap

/-- The greedy list is strictly ordered by position, so the entry before a gap
sits strictly before the entry after it. -/
theorem pos_entrySource_lt_of_adjacent
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L) (j : Fin A.pieceCount)
    {p e : Fin A.sources.length}
    (hp : previousEntry A j = some p) (he : nextEntry A j = some e) :
    pos (HalfEntry.entrySource A p) < pos (HalfEntry.entrySource A e) := by
  classical
  have hjpos : 0 < j.val := by
    rcases Nat.eq_zero_or_pos j.val with h0 | hpos
    · exfalso
      have hnone := (previousEntry_eq_none_iff A j).mpr h0
      rw [hp] at hnone
      simp at hnone
    · exact hpos
  have hjbound : j.val < A.sources.length + 1 := by
    have hj := j.isLt
    simpa only [GreedyHalfFamilyIndex.pieceCount] using hj
  have hpval : p.val = j.val - 1 := by
    have hdef : previousEntry A j = some ⟨j.val - 1, by omega⟩ := by
      simp [previousEntry, hjpos]
    rw [hp] at hdef
    exact congrArg Fin.val (Option.some.inj hdef)
  have hjlt : j.val < A.sources.length := by
    rcases Nat.lt_or_ge j.val A.sources.length with hlt | hge
    · exact hlt
    · exfalso
      have heq : j.val = A.sources.length := by omega
      have hnone := (nextEntry_eq_none_iff A j).mpr heq
      rw [he] at hnone
      simp at hnone
  have heval : e.val = j.val := by
    have hdef : nextEntry A j = some ⟨j.val, hjlt⟩ := by
      simp [nextEntry, hjlt]
    rw [he] at hdef
    exact congrArg Fin.val (Option.some.inj hdef)
  have hlt : p.val < e.val := by omega
  have hle : A.sources[p] ≤ A.sources[e] :=
    List.pairwise_iff_getElem.mp A.source_order p.val e.val p.isLt e.isLt hlt
  have hne : A.sources[p] ≠ A.sources[e] :=
    List.pairwise_iff_getElem.mp A.source_nodup p.val e.val p.isLt e.isLt hlt
  rw [HalfEntry.source_getElem_eq_pos_entrySource A p,
    HalfEntry.source_getElem_eq_pos_entrySource A e] at hle hne
  exact lt_of_le_of_ne hle hne

end HalfGap

namespace BalancedSplitData

/-! ## Consecutive parent components carry different labels -/

/-- Two distinguished first-half sides whose one-edge components are
consecutive in the parent arc have different peripheral labels: otherwise the
first component would not be maximal. -/
theorem firstTarget_label_ne_of_succ
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    {s t : ℕ} (hs : s ∈ B.firstTarget) (ht : t ∈ B.firstTarget)
    (hadj : B.firstTargetPos s + 1 = B.firstTargetPos t) :
    P.label s ≠ P.label t := by
  have hltT : B.firstTargetPos t < B.firstArc.length := by
    have hend := (B.firstArc_targetComponent ht).2.1
    omega
  have hltS : B.firstTargetPos s + 1 < B.firstArc.length := by omega
  intro hEqLabel
  have hletterT := (B.firstArc_targetComponent ht).2.2.1
    (B.firstTargetPos t) le_rfl (by omega) hltT
  have hgoal : (B.firstArc[B.firstTargetPos s + 1]'hltS).IsCompOf
      (P.label s) := by
    rw [getElem_congr_idx hadj, hEqLabel]
    exact hletterT
  exact (B.firstArc_targetComponent hs).2.2.2.2 hltS hgoal

/-! ## The two neighbours of a first-half right connector -/

/-- The letter preceding the right connector of a first-half gap child does
not carry that connector's label. -/
theorem firstGap_rightConnector_prev_exclusion
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.first j = some e)
    (hzero : 0 < (B.firstGapRight j).length) :
    ∀ q : ℕ,
      (B.firstGapLeft j).length +
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)).length = q + 1 →
      ∀ hq : q < (B.firstGapCycle j).length,
      ¬ ((B.firstGapCycle j)[q]'hq).IsCompOf
        (B.firstGapLocalLabel j ((B.firstGapLeft j).length +
          (B.firstGapFinishSide j - B.firstGapStartSide j))) := by
  classical
  intro q hq0 hq hletter
  have hlab : B.firstGapLocalLabel j ((B.firstGapLeft j).length +
      (B.firstGapFinishSide j - B.firstGapStartSide j)) =
      P.label (HalfEntry.entrySource B.brokenAssignment.index.first e) := by
    simpa using B.firstGapLocalLabel_rightConnector j e he 0 hzero
  rw [hlab] at hletter
  by_cases harc : 0 < (arcWord B.firstArc B.firstArcCut
      (B.firstGapStartSide j) (B.firstGapFinishSide j)).length
  · have hidx : q = (B.firstGapLeft j).length +
        ((arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length - 1) := by omega
    have hcycleLt : (B.firstGapLeft j).length +
        ((arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length - 1) <
        (B.firstGapCycle j).length := by omega
    have hgetEq : (B.firstGapCycle j)[q]'hq =
        (B.firstGapCycle j)[(B.firstGapLeft j).length +
          ((arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)).length - 1)]'hcycleLt :=
      getElem_congr_idx hidx
    rw [hgetEq] at hletter
    have hArcLt : (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)).length - 1 <
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length := by omega
    have hco := (isCompOf_auxiliaryCycle_arc_iff
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.first e))
      (B.firstGapLeft j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)) (B.firstGapRight j)
      (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j))
      ((arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)).length - 1) hArcLt hcycleLt).mp hletter
    exact B.firstGap_arcLast_not_isCompOf j e he harc
      (by simpa [List.get_eq_getElem] using hco)
  · have hqL : q < (B.firstGapLeft j).length := by omega
    have hprevNe : HalfGap.previousEntry B.brokenAssignment.index.first j
        ≠ none := by
      intro hnone
      have h0 : (B.firstGapLeft j).length = 0 := by
        simp only [firstGapLeft]
        rw [hnone]
        simp
      omega
    obtain ⟨p, hp'⟩ := Option.ne_none_iff_exists'.mp hprevNe
    have hp : HalfGap.previousEntry B.brokenAssignment.index.first j =
        some p := by simpa using hp'
    have hconn := B.firstGap_leftConnector_isCompOf j p hp q hqL hq
    have hconnLabel := B.firstGapLocalLabel_leftConnector j p hp q hqL
    have hconn' : ((B.firstGapCycle j)[q]'hq).IsCompOf
        (P.label (HalfEntry.entrySource
          B.brokenAssignment.index.first p)) := by
      rw [← hconnLabel]
      exact hconn
    have hEqLabel : P.label (HalfEntry.entrySource
          B.brokenAssignment.index.first p) =
        P.label (HalfEntry.entrySource
          B.brokenAssignment.index.first e) :=
      eq_of_isCompOf_of_isCompOf hconn' hletter
    have hpBroken := HalfEntry.entrySource_mem
      B.brokenAssignment.index.first p
    have heBroken := HalfEntry.entrySource_mem
      B.brokenAssignment.index.first e
    have hpTarget := (mem_brokenSet_iff.mp hpBroken).1
    have heTarget := (mem_brokenSet_iff.mp heBroken).1
    have hstartSide : B.firstGapStartSide j =
        B.firstTargetSide (HalfEntry.entrySource
          B.brokenAssignment.index.first p) + 1 := by
      simp only [firstGapStartSide]
      rw [hp]
    have hfinishSide : B.firstGapFinishSide j =
        B.firstTargetSide (HalfEntry.entrySource
          B.brokenAssignment.index.first e) := by
      simp only [firstGapFinishSide]
      rw [he]
    have hcutEnd : B.firstArcCut (B.firstGapFinishSide j) ≤
        B.firstArc.length :=
      B.firstArc_isCutPath.cut.le_length (B.firstGapFinishSide_le j)
    have harcLen : (arcWord B.firstArc B.firstArcCut
        (B.firstGapStartSide j) (B.firstGapFinishSide j)).length =
        B.firstArcCut (B.firstGapFinishSide j) -
          B.firstArcCut (B.firstGapStartSide j) :=
      length_arcWord B.firstArc B.firstArcCut hcutEnd
    have hcutStart : B.firstArcCut (B.firstGapStartSide j) =
        B.firstTargetPos (HalfEntry.entrySource
          B.brokenAssignment.index.first p) + 1 := by
      rw [hstartSide]
      exact (B.firstArcCut_target hpTarget).2
    have hcutFinish : B.firstArcCut (B.firstGapFinishSide j) =
        B.firstTargetPos (HalfEntry.entrySource
          B.brokenAssignment.index.first e) := by
      rw [hfinishSide]
      exact (B.firstArcCut_target heTarget).1
    have hposLt := HalfGap.pos_entrySource_lt_of_adjacent
      B.brokenAssignment.index.first j hp he
    have hposLt' : B.firstTargetPos (HalfEntry.entrySource
          B.brokenAssignment.index.first p) <
        B.firstTargetPos (HalfEntry.entrySource
          B.brokenAssignment.index.first e) := hposLt
    have hadj : B.firstTargetPos (HalfEntry.entrySource
          B.brokenAssignment.index.first p) + 1 =
        B.firstTargetPos (HalfEntry.entrySource
          B.brokenAssignment.index.first e) := by omega
    exact B.firstTarget_label_ne_of_succ hpTarget heTarget hadj hEqLabel

/-- The letter following the right connector of a first-half gap child does
not carry that connector's label. -/
theorem firstGap_rightConnector_next_exclusion
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.first j = some e)
    (hzero : 0 < (B.firstGapRight j).length) :
    ∀ hn : (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length + 1 <
        (B.firstGapCycle j).length,
      ¬ ((B.firstGapCycle j).get ⟨
        (B.firstGapLeft j).length +
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)).length + 1, hn⟩).IsCompOf
        (B.firstGapLocalLabel j ((B.firstGapLeft j).length +
          (B.firstGapFinishSide j - B.firstGapStartSide j))) := by
  classical
  intro hn hletter
  have hlab : B.firstGapLocalLabel j ((B.firstGapLeft j).length +
      (B.firstGapFinishSide j - B.firstGapStartSide j)) =
      P.label (HalfEntry.entrySource B.brokenAssignment.index.first e) := by
    simpa using B.firstGapLocalLabel_rightConnector j e he 0 hzero
  rw [hlab] at hletter
  have hone : (B.firstGapRight j).length = 1 := by
    have hle := B.firstGapRight_length_le_one j
    omega
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
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length + 1]'hn =
      (B.firstGapCycle j)[(B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length + 0]'hn' :=
    getElem_congr_idx (by omega)
  rw [List.get_eq_getElem, hgetEq] at hletter
  have hchord := (isCompOf_auxiliaryCycle_chord_iff
    (P.label (HalfEntry.entrySource B.brokenAssignment.index.first e))
    (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)) (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j)) 0 hsegPos hn').mp hletter
  exact B.firstGap_chordHead_not_isCompOf_nextEntry j e he hsegPos hchord

/-! ## The right connector component, unconditionally -/

/-- The right connector of a first-half gap child with a following broken
entry is a maximal one-letter component of the auxiliary cycle. -/
theorem firstGap_rightConnector_component
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.first j = some e)
    (hzero : 0 < (B.firstGapRight j).length) :
    IsComp (B.firstGapLocalLabel j ((B.firstGapLeft j).length +
        (B.firstGapFinishSide j - B.firstGapStartSide j)))
      (B.firstGapCycle j)
      (B.firstGapCut j ((B.firstGapLeft j).length +
        (B.firstGapFinishSide j - B.firstGapStartSide j)))
      (B.firstGapCut j ((B.firstGapLeft j).length +
        (B.firstGapFinishSide j - B.firstGapStartSide j) + 1)) :=
  B.firstGap_rightConnector_cycleComponent j e he hzero
    (B.firstGap_rightConnector_prev_exclusion j e he hzero)
    (B.firstGap_rightConnector_next_exclusion j e he hzero)

/-- The `rightComponent` field of `FirstGapComponentFamily`, with no residual
hypothesis: a connector range is nonempty only when the gap has a following
broken entry, and it then has length exactly one. -/
theorem firstGap_rightComponent
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (r : ℕ) (hr : r < (B.firstGapRight j).length) :
    IsComp (B.firstGapLocalLabel j ((B.firstGapLeft j).length +
        (B.firstGapFinishSide j - B.firstGapStartSide j) + r))
      (B.firstGapCycle j)
      (B.firstGapCut j ((B.firstGapLeft j).length +
        (B.firstGapFinishSide j - B.firstGapStartSide j) + r))
      (B.firstGapCut j ((B.firstGapLeft j).length +
        (B.firstGapFinishSide j - B.firstGapStartSide j) + r + 1)) := by
  classical
  have hle := B.firstGapRight_length_le_one j
  have hr0 : r = 0 := by omega
  subst hr0
  have hzero : 0 < (B.firstGapRight j).length := by omega
  have hnxt : HalfGap.nextEntry B.brokenAssignment.index.first j ≠ none := by
    intro hnone
    have h0 : (B.firstGapRight j).length = 0 := by
      simp only [firstGapRight]
      rw [hnone]
      simp
    omega
  obtain ⟨e, he'⟩ := Option.ne_none_iff_exists'.mp hnxt
  have he : HalfGap.nextEntry B.brokenAssignment.index.first j = some e := by
    simpa using he'
  simpa using B.firstGap_rightConnector_component j e he hzero

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
