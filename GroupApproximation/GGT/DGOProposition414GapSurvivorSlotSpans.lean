import GroupApproximation.GGT.DGOProposition414GapPartnerSlotSpans
import GroupApproximation.GGT.DGOProposition414GapSurvivorSlots

/-!
# Spans of inherited survivor slots

A surviving distinguished component is copied into the inherited arc block of
its canonical gap child.  This module identifies that child-side span with the
original polygon-side span.  It is the type-(1) factor calculation in
Dahmani--Guirardel--Osin Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- A first-half target position is a genuine inherited-arc letter index. -/
theorem firstTargetPos_lt_firstArc_length
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.firstTarget) :
    B.firstTargetPos s < B.firstArc.length := by
  have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have hEnd : B.refinedCut (B.secondSide + 2) ≤ P.word.length := by
    rw [hright]
    exact B.secondVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
  have hlt := B.firstTargetPos_lt hs
  rw [firstArc, length_arcWord P.word B.refinedCut hEnd]
  simpa only [firstArcLength, hleft, hright] using hlt

/-- A wrapped-half target position is a genuine inherited-arc letter index. -/
theorem secondTargetPos_lt_secondArc_length
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.secondTarget) :
    B.secondTargetPos s < B.secondArc.length := by
  have hfirstLe : B.firstVertex ≤ P.word.length :=
    B.firstVertex_mem.2.trans
      ((P.polygonCut.mono_le (Nat.succ_le_iff.mpr B.side_order)).trans
        (B.secondVertex_mem.1.trans
          (B.secondVertex_mem.2.trans
            (P.polygonCut.le_length
              (Nat.succ_le_iff.mpr B.secondSide_lt)))))
  have hlt := B.secondTargetPos_lt hs
  simpa [secondArc, secondArcLength, Nat.min_eq_left hfirstLe] using hlt

/-- The inherited first-arc letter at a target is the original target span. -/
theorem firstTarget_arcLetter_val_eq_span
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.firstTarget) :
    (B.firstArc[B.firstTargetPos s]'
      (B.firstTargetPos_lt_firstArc_length hs)).val = P.span s := by
  have hsP : s ∈ P.target := (Finset.mem_filter.mp hs).1
  have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have hEnd : B.refinedCut (B.secondSide + 2) ≤ P.word.length := by
    rw [hright]
    exact B.secondVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
  have hpos : B.firstVertex + B.firstTargetPos s = P.cut s := by
    have hsData := Finset.mem_filter.mp hs
    unfold targetInFirstArc at hsData
    simp only [firstTargetPos]
    omega
  have hi : B.firstTargetPos s <
      B.refinedCut (B.secondSide + 2) -
        B.refinedCut (B.firstSide + 1) := by
    have hlt := B.firstTargetPos_lt hs
    simpa only [firstArcLength, hleft, hright] using hlt
  have hletter := getElem_arcWord P.word B.refinedCut hEnd hi
    (B.firstTargetPos_lt_firstArc_length hs)
  have hcutLt : P.cut s < P.word.length := by
    have hc := P.target_component s hsP
    exact hc.1.trans_le hc.2.1
  have hletter' :
      B.firstArc[B.firstTargetPos s]'
          (B.firstTargetPos_lt_firstArc_length hs) =
        P.word[P.cut s]'hcutLt := by
    change (arcWord P.word B.refinedCut (B.firstSide + 1)
      (B.secondSide + 2))[B.firstTargetPos s]'_ = _
    rw [hletter]
    exact getElem_congr_idx (by rw [hleft, hpos])
  rw [hletter']
  unfold SumBoundInput.span
  rw [P.target_edge s hsP,
    vertex_succ P.word P.basepoint (P.cut s) hcutLt]
  group

/-- The inherited wrapped-arc letter at a target is the original target span. -/
theorem secondTarget_arcLetter_val_eq_span
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.secondTarget) :
    (B.secondArc[B.secondTargetPos s]'
      (B.secondTargetPos_lt_secondArc_length hs)).val = P.span s := by
  have hsP : s ∈ P.target := (Finset.mem_filter.mp hs).1
  have hcutLt : P.cut s < P.word.length := by
    have hc := P.target_component s hsP
    exact hc.1.trans_le hc.2.1
  have hletter :
      B.secondArc[B.secondTargetPos s]'
          (B.secondTargetPos_lt_secondArc_length hs) =
        P.word[P.cut s]'hcutLt := by
    by_cases hafter : B.secondVertex ≤ P.cut s
    · have hdrop : B.secondTargetPos s <
          (P.word.drop B.secondVertex).length := by
        rw [List.length_drop]
        simp only [secondTargetPos, if_pos hafter]
        omega
      change (P.word.drop B.secondVertex ++ P.word.take B.firstVertex)[
        B.secondTargetPos s]'_ = _
      rw [List.getElem_append_left hdrop, List.getElem_drop]
      exact getElem_congr_idx (by
        simp only [secondTargetPos, if_pos hafter]
        omega)
    · have hbefore := (B.outside_firstArc_cases hs).resolve_right hafter
      have hdropLe : (P.word.drop B.secondVertex).length ≤
          B.secondTargetPos s := by
        rw [List.length_drop]
        simp only [secondTargetPos, if_neg hafter]
        omega
      have hcutFirst : P.cut s < B.firstVertex := by
        have hedge := P.target_edge s hsP
        rw [hedge] at hbefore
        omega
      change (P.word.drop B.secondVertex ++ P.word.take B.firstVertex)[
        B.secondTargetPos s]'_ = _
      rw [List.getElem_append_right hdropLe]
      have hindex : B.secondTargetPos s -
          (P.word.drop B.secondVertex).length = P.cut s := by
        rw [List.length_drop]
        simp only [secondTargetPos, if_neg hafter]
        omega
      rw [getElem_congr_idx hindex, List.getElem_take]
  rw [hletter]
  unfold SumBoundInput.span
  rw [P.target_edge s hsP,
    vertex_succ P.word P.basepoint (P.cut s) hcutLt]
  group

/-- A surviving first-half slot has exactly the original component span. -/
theorem firstSurvivorSlot_span
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ B.firstTarget)
    (hsurvives : B.componentPlacement.firstSurvives s) :
    optionalTargetSlotSpan (some (B.firstSurvivorSlot C hs hsurvives)) =
      P.span s := by
  let Q := (B.gapIntervalsOfConfigurations C).toPathInput
  let j := B.firstSurvivorGapOwner hs hsurvives
  let r := B.firstTargetSide s - B.firstGapStartSide j
  have hsGap := Finset.mem_filter.mp
    (B.firstSurvivorGapOwner_mem hs hsurvives)
  have hr : r < B.firstGapFinishSide j - B.firstGapStartSide j := by
    dsimp [r]
    omega
  have hrStart : B.firstGapStartSide j + r = B.firstTargetSide s := by
    dsimp [r]
    omega
  have hrSucc : B.firstGapStartSide j + (r + 1) =
      B.firstTargetSide s + 1 := by omega
  have htargetCut := B.firstArcCut_target hs
  have hedge : (Q.first j).arcCut (r + 1) =
      (Q.first j).arcCut r + 1 := by
    change B.firstArcCut (B.firstGapStartSide j + (r + 1)) -
        B.firstArcCut (B.firstGapStartSide j) =
      (B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j)) + 1
    rw [hrStart, hrSucc, htargetCut.1, htargetCut.2]
    have hbase := B.firstArc_isCutPath.cut.mono_le hsGap.2.1
    omega
  change (Q.first j).certificate.sideSpan
      ((B.firstGapLeft j).length + r) = P.span s
  rw [(Q.first j).arc_sideSpan_eq_letter r hr hedge]
  have hfinishLe := B.firstGapFinishSide_le j
  have hcutEnd := B.firstArc_isCutPath.cut.le_length hfinishLe
  have hlocal : (Q.first j).arcCut r <
      B.firstArcCut (B.firstGapFinishSide j) -
        B.firstArcCut (B.firstGapStartSide j) := by
    change B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j) < _
    have hmono := B.firstArc_isCutPath.cut.mono_le hsGap.2.1
    rw [hrStart, htargetCut.1]
    have hfinishMono := B.firstArc_isCutPath.cut.mono_le hsGap.2.2.le
    omega
  rw [getElem_arcWord B.firstArc B.firstArcCut hcutEnd hlocal]
  have hindex : B.firstArcCut (B.firstGapStartSide j) +
      (Q.first j).arcCut r = B.firstTargetPos s := by
    change B.firstArcCut (B.firstGapStartSide j) +
        (B.firstArcCut (B.firstGapStartSide j + r) -
          B.firstArcCut (B.firstGapStartSide j)) = B.firstTargetPos s
    rw [hrStart, htargetCut.1]
    have hmono := B.firstArc_isCutPath.cut.mono_le hsGap.2.1
    omega
  rw [getElem_congr_idx hindex]
  exact B.firstTarget_arcLetter_val_eq_span hs

/-- A surviving wrapped-half slot has exactly the original component span. -/
theorem secondSurvivorSlot_span
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : GapComponentConfigurations hsymm hδ P B)
    (hs : s ∈ B.secondTarget)
    (hsurvives : B.componentPlacement.secondSurvives s) :
    optionalTargetSlotSpan (some (B.secondSurvivorSlot C hs hsurvives)) =
      P.span s := by
  let Q := (B.gapIntervalsOfConfigurations C).toPathInput
  let j := B.secondSurvivorGapOwner hs hsurvives
  let r := B.secondTargetSide s - B.secondGapStartSide j
  have hsGap := Finset.mem_filter.mp
    (B.secondSurvivorGapOwner_mem hs hsurvives)
  have hr : r < B.secondGapFinishSide j - B.secondGapStartSide j := by
    dsimp [r]
    omega
  have hrStart : B.secondGapStartSide j + r = B.secondTargetSide s := by
    dsimp [r]
    omega
  have hrSucc : B.secondGapStartSide j + (r + 1) =
      B.secondTargetSide s + 1 := by omega
  have htargetCut := B.secondArcCut_target hs
  have hedge : (Q.second j).arcCut (r + 1) =
      (Q.second j).arcCut r + 1 := by
    change B.secondArcCut (B.secondGapStartSide j + (r + 1)) -
        B.secondArcCut (B.secondGapStartSide j) =
      (B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j)) + 1
    rw [hrStart, hrSucc, htargetCut.1, htargetCut.2]
    have hbase := B.secondArc_isCutPath.cut.mono_le hsGap.2.1
    omega
  change (Q.second j).certificate.sideSpan
      ((B.secondGapLeft j).length + r) = P.span s
  rw [(Q.second j).arc_sideSpan_eq_letter r hr hedge]
  have hfinishLe := B.secondGapFinishSide_le j
  have hcutEnd := B.secondArc_isCutPath.cut.le_length hfinishLe
  have hlocal : (Q.second j).arcCut r <
      B.secondArcCut (B.secondGapFinishSide j) -
        B.secondArcCut (B.secondGapStartSide j) := by
    change B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j) < _
    have hmono := B.secondArc_isCutPath.cut.mono_le hsGap.2.1
    rw [hrStart, htargetCut.1]
    have hfinishMono := B.secondArc_isCutPath.cut.mono_le hsGap.2.2.le
    omega
  rw [getElem_arcWord B.secondArc B.secondArcCut hcutEnd hlocal]
  have hindex : B.secondArcCut (B.secondGapStartSide j) +
      (Q.second j).arcCut r = B.secondTargetPos s := by
    change B.secondArcCut (B.secondGapStartSide j) +
        (B.secondArcCut (B.secondGapStartSide j + r) -
          B.secondArcCut (B.secondGapStartSide j)) = B.secondTargetPos s
    rw [hrStart, htargetCut.1]
    have hmono := B.secondArc_isCutPath.cut.mono_le hsGap.2.1
    omega
  rw [getElem_congr_idx hindex]
  exact B.secondTarget_arcLetter_val_eq_span hs

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
