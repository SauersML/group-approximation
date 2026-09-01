import GroupApproximation.GGT.DGOProposition414GapIndex

/-!
# Endpoint closure of the canonical balanced-surgery gaps

The exact source endpoint retained by the connector producer is the endpoint
of the distinguished inherited edge.  Consequently the reversed left
connector, inherited subarc, and right connector concatenate from the named
global-chord finish vertex to the named global-chord start vertex.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- The start vertex of a broken first-half edge is its inherited-arc cut. -/
theorem firstBroken_sourceStart_vertex_arc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    vertex B.firstBase B.firstWord (B.componentPlacement.firstPos s) =
      vertex B.firstBase B.firstArc (B.firstArcCut (B.firstTargetSide s)) := by
  have hsTarget := (mem_brokenSet_iff.mp hs).1
  have hcut := (B.firstArcCut_target hsTarget).1
  have hpos : B.componentPlacement.firstPos s = B.firstTargetPos s := rfl
  have hle : B.firstTargetPos s ≤ B.firstArc.length := by
    rw [← hcut]
    exact B.firstArc_isCutPath.cut.le_length
      (B.firstTargetSide_lt hsTarget).le
  rw [hpos, hcut]
  exact vertex_append_left B.firstBase B.firstArc (revWord B.chord) hle

/-- The exact end vertex of a broken first-half edge is the following
inherited-arc cut. -/
theorem firstBroken_sourceEnd_vertex_arc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    vertex B.firstBase B.firstWord (B.firstBrokenConnectors s hs).sourceEnd =
      vertex B.firstBase B.firstArc
        (B.firstArcCut (B.firstTargetSide s + 1)) := by
  have hsTarget := (mem_brokenSet_iff.mp hs).1
  have hcut := (B.firstArcCut_target hsTarget).2
  have hpos : B.componentPlacement.firstPos s = B.firstTargetPos s := rfl
  have hend := (B.firstBrokenConnectors s hs).source_end_eq
  have hle : B.firstTargetPos s + 1 ≤ B.firstArc.length := by
    rw [← hcut]
    exact B.firstArc_isCutPath.cut.le_length
      (show B.firstTargetSide s + 1 ≤
        B.secondSide - B.firstSide + 1 by
        exact Nat.succ_le_iff.mpr (B.firstTargetSide_lt hsTarget))
  rw [hend, hpos, hcut]
  exact vertex_append_left B.firstBase B.firstArc (revWord B.chord) hle

/-- The start vertex of a broken wrapped-half edge is its inherited-arc cut. -/
theorem secondBroken_sourceStart_vertex_arc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    vertex B.secondBase B.secondWord (B.componentPlacement.secondPos s) =
      vertex B.secondBase B.secondArc
        (B.secondArcCut (B.secondTargetSide s)) := by
  have hsTarget := (mem_brokenSet_iff.mp hs).1
  have hcut := (B.secondArcCut_target hsTarget).1
  have hpos : B.componentPlacement.secondPos s = B.secondTargetPos s := rfl
  have hle : B.secondTargetPos s ≤ B.secondArc.length := by
    rw [← hcut]
    exact B.secondArc_isCutPath.cut.le_length
      (B.secondTargetSide_lt hsTarget).le
  rw [hpos, hcut]
  have hword : B.secondWord = B.secondArc ++ B.chord := by
    have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
      simp [refinedCut, splitPairCut_left B.side_order]
    have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
      simp [refinedCut, splitPairCut_right]
    unfold secondWord secondArc
    simp only [secondHalf]
    rw [hleft, hright]
  rw [hword]
  exact vertex_append_left B.secondBase B.secondArc B.chord hle

/-- The exact end vertex of a broken wrapped-half edge is the following
inherited-arc cut. -/
theorem secondBroken_sourceEnd_vertex_arc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    vertex B.secondBase B.secondWord (B.secondBrokenConnectors s hs).sourceEnd =
      vertex B.secondBase B.secondArc
        (B.secondArcCut (B.secondTargetSide s + 1)) := by
  have hsTarget := (mem_brokenSet_iff.mp hs).1
  have hcut := (B.secondArcCut_target hsTarget).2
  have hpos : B.componentPlacement.secondPos s = B.secondTargetPos s := rfl
  have hend := (B.secondBrokenConnectors s hs).source_end_eq
  have hle : B.secondTargetPos s + 1 ≤ B.secondArc.length := by
    rw [← hcut]
    exact B.secondArc_isCutPath.cut.le_length
      (show B.secondTargetSide s + 1 ≤
        (n - B.secondSide) + B.firstSide + 1 by
        exact Nat.succ_le_iff.mpr (B.secondTargetSide_lt hsTarget))
  rw [hend, hpos, hcut]
  have hword : B.secondWord = B.secondArc ++ B.chord := by
    have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
      simp [refinedCut, splitPairCut_left B.side_order]
    have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
      simp [refinedCut, splitPairCut_right]
    unfold secondWord secondArc
    simp only [secondHalf]
    rw [hleft, hright]
  rw [hword]
  exact vertex_append_left B.secondBase B.secondArc B.chord hle

/-- Source order on the first inherited arc is strict side order. -/
theorem firstTargetSide_lt_of_pos_lt
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s t : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.firstTarget) (ht : t ∈ B.firstTarget)
    (hpos : B.firstTargetPos s < B.firstTargetPos t) :
    B.firstTargetSide s < B.firstTargetSide t := by
  by_contra hnot
  have hmono := B.firstArc_isCutPath.cut.mono_le
    (show B.firstTargetSide t ≤ B.firstTargetSide s by omega)
  rw [(B.firstArcCut_target ht).1, (B.firstArcCut_target hs).1] at hmono
  omega

/-- Source order on the wrapped inherited arc is strict side order. -/
theorem secondTargetSide_lt_of_pos_lt
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s t : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.secondTarget) (ht : t ∈ B.secondTarget)
    (hpos : B.secondTargetPos s < B.secondTargetPos t) :
    B.secondTargetSide s < B.secondTargetSide t := by
  by_contra hnot
  have hmono := B.secondArc_isCutPath.cut.mono_le
    (show B.secondTargetSide t ≤ B.secondTargetSide s by omega)
  rw [(B.secondArcCut_target ht).1, (B.secondArcCut_target hs).1] at hmono
  omega

private theorem previousEntry_val_lt_nextEntry_val
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L) (j : Fin A.pieceCount)
    {e f : Fin A.sources.length}
    (he : HalfGap.previousEntry A j = some e)
    (hf : HalfGap.nextEntry A j = some f) : e.val < f.val := by
  have heval : e.val = j.val - 1 := by
    unfold HalfGap.previousEntry at he
    split at he
    · simpa using (congrArg (fun x => Option.map Fin.val x) he).symm
    · simp at he
  have hfval : f.val = j.val := by
    unfold HalfGap.nextEntry at hf
    split at hf
    · simpa using (congrArg (fun x => Option.map Fin.val x) hf).symm
    · simp at hf
  have hjpos : 0 < j.val := by
    have hne : HalfGap.previousEntry A j ≠ none := by rw [he]; simp
    exact Nat.pos_of_ne_zero
      ((HalfGap.previousEntry_eq_none_iff A j).not.mp hne)
  omega

/-- Every first-half gap names a genuine forward inherited subarc. -/
theorem firstGap_side_order
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    B.firstGapStartSide j ≤ B.firstGapFinishSide j := by
  classical
  let A := B.brokenAssignment.index.first
  cases he : HalfGap.previousEntry A j with
  | none =>
      have hs : B.firstGapStartSide j = 0 := by
        simp only [firstGapStartSide]
        rw [he]
      rw [hs]
      exact Nat.zero_le _
  | some e =>
      let s := HalfEntry.entrySource A e
      let hs := HalfEntry.entrySource_mem A e
      cases hf : HalfGap.nextEntry A j with
      | none =>
          have hstart : B.firstGapStartSide j = B.firstTargetSide s + 1 := by
            simp only [firstGapStartSide]
            rw [he]
          have hfinish : B.firstGapFinishSide j =
              B.secondSide - B.firstSide + 1 := by
            simp only [firstGapFinishSide]
            rw [hf]
          rw [hstart, hfinish]
          exact Nat.succ_le_iff.mpr (B.firstTargetSide_lt
            (mem_brokenSet_iff.mp hs).1)
      | some f =>
          let t := HalfEntry.entrySource A f
          let ht := HalfEntry.entrySource_mem A f
          have hef := previousEntry_val_lt_nextEntry_val A j he hf
          have hle := List.pairwise_iff_getElem.mp A.source_order
            e.val f.val e.isLt f.isLt hef
          have hne := List.pairwise_iff_getElem.mp A.source_nodup
            e.val f.val e.isLt f.isLt hef
          have hpos : B.componentPlacement.firstPos s <
              B.componentPlacement.firstPos t := by
            rw [← HalfEntry.source_getElem_eq_pos_entrySource A e,
              ← HalfEntry.source_getElem_eq_pos_entrySource A f]
            exact lt_of_le_of_ne hle hne
          have hside := B.firstTargetSide_lt_of_pos_lt
            (mem_brokenSet_iff.mp hs).1 (mem_brokenSet_iff.mp ht).1 hpos
          have hstart : B.firstGapStartSide j = B.firstTargetSide s + 1 := by
            simp only [firstGapStartSide]
            rw [he]
          have hfinish : B.firstGapFinishSide j = B.firstTargetSide t := by
            simp only [firstGapFinishSide]
            rw [hf]
          rw [hstart, hfinish]
          exact Nat.succ_le_iff.mpr hside

/-- Every wrapped-half gap names a genuine forward inherited subarc. -/
theorem secondGap_side_order
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    B.secondGapStartSide j ≤ B.secondGapFinishSide j := by
  classical
  let A := B.brokenAssignment.index.second
  cases he : HalfGap.previousEntry A j with
  | none =>
      have hs : B.secondGapStartSide j = 0 := by
        simp only [secondGapStartSide]
        rw [he]
      rw [hs]
      exact Nat.zero_le _
  | some e =>
      let s := HalfEntry.entrySource A e
      let hs := HalfEntry.entrySource_mem A e
      cases hf : HalfGap.nextEntry A j with
      | none =>
          have hstart : B.secondGapStartSide j = B.secondTargetSide s + 1 := by
            simp only [secondGapStartSide]
            rw [he]
          have hfinish : B.secondGapFinishSide j =
              (n - B.secondSide) + B.firstSide + 1 := by
            simp only [secondGapFinishSide]
            rw [hf]
          rw [hstart, hfinish]
          exact Nat.succ_le_iff.mpr (B.secondTargetSide_lt
            (mem_brokenSet_iff.mp hs).1)
      | some f =>
          let t := HalfEntry.entrySource A f
          let ht := HalfEntry.entrySource_mem A f
          have hef := previousEntry_val_lt_nextEntry_val A j he hf
          have hle := List.pairwise_iff_getElem.mp A.source_order
            e.val f.val e.isLt f.isLt hef
          have hne := List.pairwise_iff_getElem.mp A.source_nodup
            e.val f.val e.isLt f.isLt hef
          have hpos : B.componentPlacement.secondPos s <
              B.componentPlacement.secondPos t := by
            rw [← HalfEntry.source_getElem_eq_pos_entrySource A e,
              ← HalfEntry.source_getElem_eq_pos_entrySource A f]
            exact lt_of_le_of_ne hle hne
          have hside := B.secondTargetSide_lt_of_pos_lt
            (mem_brokenSet_iff.mp hs).1 (mem_brokenSet_iff.mp ht).1 hpos
          have hstart : B.secondGapStartSide j = B.secondTargetSide s + 1 := by
            simp only [secondGapStartSide]
            rw [he]
          have hfinish : B.secondGapFinishSide j = B.secondTargetSide t := by
            simp only [secondGapFinishSide]
            rw [hf]
          rw [hstart, hfinish]
          exact Nat.succ_le_iff.mpr hside

/-- The first-half gap's reversed left connector lands at its inherited start
cut. -/
theorem firstGap_arcBase
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    vertex B.firstBase B.chord (B.firstGapChordFinish j) *
        RelLetter.listVal (revWord (B.firstGapLeft j)) =
      vertex B.firstBase B.firstArc (B.firstArcCut (B.firstGapStartSide j)) := by
  classical
  cases hprev : HalfGap.previousEntry B.brokenAssignment.index.first j with
  | none =>
      have hfinish : B.firstGapChordFinish j = 0 := by
        simp only [firstGapChordFinish]
        rw [hprev]
      have hleft : B.firstGapLeft j = [] := by
        simp only [firstGapLeft]
        rw [hprev]
      have hside : B.firstGapStartSide j = 0 := by
        simp only [firstGapStartSide]
        rw [hprev]
      rw [hfinish, hleft, hside, vertex_zero, listVal_revWord,
        RelLetter.listVal_nil, inv_one, mul_one,
        B.firstArc_isCutPath.cut.start, vertex_zero]
  | some e =>
      let s := HalfEntry.entrySource B.brokenAssignment.index.first e
      let hs := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
      have hend := B.firstBrokenConnectors_end_value_global s hs
      have harc := B.firstBroken_sourceEnd_vertex_arc s hs
      have hfinish : B.firstGapChordFinish j =
          B.brokenAssignment.first.partner s := by
        simp only [firstGapChordFinish]
        rw [hprev]
      have hleft : B.firstGapLeft j =
          (B.firstBrokenConnectors s hs).endConnector := by
        simp only [firstGapLeft]
        rw [hprev]
      have hside : B.firstGapStartSide j = B.firstTargetSide s + 1 := by
        simp only [firstGapStartSide]
        rw [hprev]
      rw [hfinish, hleft, hside]
      rw [listVal_revWord, hend, harc]
      group

/-- The right connector of a first-half gap reaches its named chord vertex. -/
theorem firstGap_arcFinish
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    vertex B.firstBase B.firstArc (B.firstArcCut (B.firstGapFinishSide j)) *
        RelLetter.listVal (B.firstGapRight j) =
      vertex B.firstBase B.chord (B.firstGapChordStart j) := by
  classical
  cases hnext : HalfGap.nextEntry B.brokenAssignment.index.first j with
  | none =>
      have hcut := B.firstArc_isCutPath.cut.finish
      have harc := B.firstArc_endpoint
      have hchord := B.chord_geodesic.2.1
      have hfinish : B.firstGapFinishSide j =
          B.secondSide - B.firstSide + 1 := by
        simp only [firstGapFinishSide]
        rw [hnext]
      have hright : B.firstGapRight j = [] := by
        simp only [firstGapRight]
        rw [hnext]
      have hstart : B.firstGapChordStart j = B.chord.length := by
        simp only [firstGapChordStart]
        rw [hnext]
      rw [hfinish, hright, hstart, RelLetter.listVal_nil, mul_one]
      rw [hcut, vertex_length, harc]
      rw [vertex_length]
      exact hchord.symm
  | some e =>
      let s := HalfEntry.entrySource B.brokenAssignment.index.first e
      let hs := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
      have hstart := B.firstBrokenConnectors_start_value_global s hs
      have harc := B.firstBroken_sourceStart_vertex_arc s hs
      have hfinish : B.firstGapFinishSide j = B.firstTargetSide s := by
        simp only [firstGapFinishSide]
        rw [hnext]
      have hright : B.firstGapRight j =
          (B.firstBrokenConnectors s hs).startConnector := by
        simp only [firstGapRight]
        rw [hnext]
      have hchordStart : B.firstGapChordStart j =
          B.brokenAssignment.first.partner s + 1 := by
        simp only [firstGapChordStart]
        rw [hnext]
      rw [hfinish, hright, hchordStart]
      rw [← harc, hstart]
      group

/-- The complete first-half prefix (left connector, inherited subarc, right
connector) has exactly the endpoints required by `AuxiliaryIntervalOnChord`. -/
theorem firstGap_prefix_endpoint
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    vertex B.firstBase B.chord (B.firstGapChordFinish j) *
        RelLetter.listVal
          ((revWord (B.firstGapLeft j) ++
            arcWord B.firstArc B.firstArcCut
              (B.firstGapStartSide j) (B.firstGapFinishSide j)) ++
            B.firstGapRight j) =
      vertex B.firstBase B.chord (B.firstGapChordStart j) := by
  have hside := B.firstGap_side_order j
  have hbase := B.firstGap_arcBase j
  have hfinish := B.firstGap_arcFinish j
  rw [listVal_append, listVal_append,
    listVal_arcWord B.firstArc B.firstBase B.firstArcCut
      (B.firstArc_isCutPath.cut.mono_le hside)]
  calc
    _ = (vertex B.firstBase B.chord (B.firstGapChordFinish j) *
          RelLetter.listVal (revWord (B.firstGapLeft j))) *
        ((vertex B.firstBase B.firstArc
          (B.firstArcCut (B.firstGapStartSide j)))⁻¹ *
          vertex B.firstBase B.firstArc
            (B.firstArcCut (B.firstGapFinishSide j))) *
        RelLetter.listVal (B.firstGapRight j) := by group
    _ = vertex B.firstBase B.firstArc
          (B.firstArcCut (B.firstGapFinishSide j)) *
        RelLetter.listVal (B.firstGapRight j) := by rw [hbase]; group
    _ = _ := hfinish

/-- The wrapped-half gap's reversed left connector lands at its inherited
start cut. -/
theorem secondGap_arcBase
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    vertex B.firstBase B.chord (B.secondGapChordFinish j) *
        RelLetter.listVal (revWord (B.secondGapLeft j)) =
      vertex B.secondBase B.secondArc
        (B.secondArcCut (B.secondGapStartSide j)) := by
  classical
  cases hprev : HalfGap.previousEntry B.brokenAssignment.index.second j with
  | none =>
      have hfinish : B.secondGapChordFinish j = B.chord.length := by
        simp only [secondGapChordFinish]
        rw [hprev]
      have hleft : B.secondGapLeft j = [] := by
        simp only [secondGapLeft]
        rw [hprev]
      have hside : B.secondGapStartSide j = 0 := by
        simp only [secondGapStartSide]
        rw [hprev]
      have hchord := B.chord_geodesic.2.1
      change B.firstBase * RelLetter.listVal B.chord = B.secondBase at hchord
      rw [hfinish, hleft, hside, listVal_revWord, RelLetter.listVal_nil,
        inv_one, mul_one, vertex_length, hchord,
        B.secondArc_isCutPath.cut.start, vertex_zero]
  | some e =>
      let s := HalfEntry.entrySource B.brokenAssignment.index.second e
      let hs := HalfEntry.entrySource_mem B.brokenAssignment.index.second e
      have hend := B.secondBrokenConnectors_end_value_global s hs
      have harc := B.secondBroken_sourceEnd_vertex_arc s hs
      have hfinish : B.secondGapChordFinish j =
          B.brokenAssignment.second.partner s + 1 := by
        simp only [secondGapChordFinish]
        rw [hprev]
      have hleft : B.secondGapLeft j =
          (B.secondBrokenConnectors s hs).endConnector := by
        simp only [secondGapLeft]
        rw [hprev]
      have hside : B.secondGapStartSide j = B.secondTargetSide s + 1 := by
        simp only [secondGapStartSide]
        rw [hprev]
      rw [hfinish, hleft, hside, listVal_revWord, hend, harc]
      group

/-- The right connector of a wrapped-half gap reaches its named chord
vertex. -/
theorem secondGap_arcFinish
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    vertex B.secondBase B.secondArc
        (B.secondArcCut (B.secondGapFinishSide j)) *
        RelLetter.listVal (B.secondGapRight j) =
      vertex B.firstBase B.chord (B.secondGapChordStart j) := by
  classical
  cases hnext : HalfGap.nextEntry B.brokenAssignment.index.second j with
  | none =>
      have hcut := B.secondArc_isCutPath.cut.finish
      have harc := B.secondArc_endpoint
      have hfinish : B.secondGapFinishSide j =
          (n - B.secondSide) + B.firstSide + 1 := by
        simp only [secondGapFinishSide]
        rw [hnext]
      have hright : B.secondGapRight j = [] := by
        simp only [secondGapRight]
        rw [hnext]
      have hstart : B.secondGapChordStart j = 0 := by
        simp only [secondGapChordStart]
        rw [hnext]
      rw [hfinish, hright, hstart, RelLetter.listVal_nil, mul_one,
        hcut, vertex_length, harc, vertex_zero]
  | some e =>
      let s := HalfEntry.entrySource B.brokenAssignment.index.second e
      let hs := HalfEntry.entrySource_mem B.brokenAssignment.index.second e
      have hstart := B.secondBrokenConnectors_start_value_global s hs
      have harc := B.secondBroken_sourceStart_vertex_arc s hs
      have hfinish : B.secondGapFinishSide j = B.secondTargetSide s := by
        simp only [secondGapFinishSide]
        rw [hnext]
      have hright : B.secondGapRight j =
          (B.secondBrokenConnectors s hs).startConnector := by
        simp only [secondGapRight]
        rw [hnext]
      have hchordStart : B.secondGapChordStart j =
          B.brokenAssignment.second.partner s := by
        simp only [secondGapChordStart]
        rw [hnext]
      rw [hfinish, hright, hchordStart, ← harc, hstart]
      group

/-- The complete wrapped-half prefix has exactly the endpoints required by
`AuxiliaryIntervalOnChord`. -/
theorem secondGap_prefix_endpoint
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    vertex B.firstBase B.chord (B.secondGapChordFinish j) *
        RelLetter.listVal
          ((revWord (B.secondGapLeft j) ++
            arcWord B.secondArc B.secondArcCut
              (B.secondGapStartSide j) (B.secondGapFinishSide j)) ++
            B.secondGapRight j) =
      vertex B.firstBase B.chord (B.secondGapChordStart j) := by
  have hside := B.secondGap_side_order j
  have hbase := B.secondGap_arcBase j
  have hfinish := B.secondGap_arcFinish j
  rw [listVal_append, listVal_append,
    listVal_arcWord B.secondArc B.secondBase B.secondArcCut
      (B.secondArc_isCutPath.cut.mono_le hside)]
  calc
    _ = (vertex B.firstBase B.chord (B.secondGapChordFinish j) *
          RelLetter.listVal (revWord (B.secondGapLeft j))) *
        ((vertex B.secondBase B.secondArc
          (B.secondArcCut (B.secondGapStartSide j)))⁻¹ *
          vertex B.secondBase B.secondArc
            (B.secondArcCut (B.secondGapFinishSide j))) *
        RelLetter.listVal (B.secondGapRight j) := by group
    _ = vertex B.secondBase B.secondArc
          (B.secondArcCut (B.secondGapFinishSide j)) *
        RelLetter.listVal (B.secondGapRight j) := by rw [hbase]; group
    _ = _ := hfinish

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
