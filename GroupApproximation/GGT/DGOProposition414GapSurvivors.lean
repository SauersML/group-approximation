import GroupApproximation.GGT.DGOProposition414GapLocalLabel

/-!
# Targets retained inside a gap are surviving components

The source list contains every broken component and is ordered by its half-word
position.  Consequently no broken source can lie strictly between the two
entries bounding a gap.  The canonical inherited targets placed in that gap
therefore already carry the full-half isolation certificate.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace HalfGap

/-- No source of the greedy enumeration lies strictly between the entries
adjacent to one gap. -/
theorem not_mem_of_strict_between
    {I : Finset ℕ} {pos partner : ℕ → ℕ} {L : ℕ}
    (A : GreedyHalfFamilyIndex I pos partner L) (j : Fin A.pieceCount)
    (s : ℕ) (hs : s ∈ I)
    (hlower : ∀ e : Fin A.sources.length,
      previousEntry A j = some e → pos (HalfEntry.entrySource A e) < pos s)
    (hupper : ∀ e : Fin A.sources.length,
      nextEntry A j = some e → pos s < pos (HalfEntry.entrySource A e)) :
    False := by
  have hmem : pos s ∈ A.sources := (A.source_mem (pos s)).mpr ⟨s, hs, rfl⟩
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hmem
  by_cases hkj : k < j.val
  · have hjpos : 0 < j.val := by omega
    let e : Fin A.sources.length := ⟨j.val - 1, by
      have hj := j.isLt
      simp only [GreedyHalfFamilyIndex.pieceCount] at hj
      omega⟩
    have hprev : previousEntry A j = some e := by
      simp [previousEntry, hjpos, e]
    have hke : k ≤ e.val := by dsimp [e]; omega
    have hle : A.sources[k] ≤ A.sources[e] := by
      by_cases heq : k = e.val
      · have hfin : (⟨k, hk⟩ : Fin A.sources.length) = e := Fin.ext heq
        change A.sources.get ⟨k, hk⟩ ≤ A.sources.get e
        rw [hfin]
      · exact List.pairwise_iff_getElem.mp A.source_order
          k e.val hk e.isLt (lt_of_le_of_ne hke heq)
    rw [hget, HalfEntry.source_getElem_eq_pos_entrySource] at hle
    exact (not_lt_of_ge hle) (hlower e hprev)
  · have hjk : j.val ≤ k := by omega
    have hjlen : j.val < A.sources.length := hjk.trans_lt hk
    let e : Fin A.sources.length := ⟨j.val, hjlen⟩
    have hnext : nextEntry A j = some e := by
      simp [nextEntry, hjlen, e]
    have hle : A.sources[e] ≤ A.sources[k] := by
      by_cases heq : j.val = k
      · have hfin : e = (⟨k, hk⟩ : Fin A.sources.length) := Fin.ext heq
        change A.sources.get e ≤ A.sources.get ⟨k, hk⟩
        rw [hfin]
      · exact List.pairwise_iff_getElem.mp A.source_order
          e.val k e.isLt hk (lt_of_le_of_ne hjk heq)
    rw [hget, HalfEntry.source_getElem_eq_pos_entrySource] at hle
    exact (not_lt_of_ge hle) (hupper e hnext)

end HalfGap

namespace BalancedSplitData

theorem firstTargetPos_lt_of_side_lt
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    {s t : ℕ} (hs : s ∈ B.firstTarget) (ht : t ∈ B.firstTarget)
    (hside : B.firstTargetSide s < B.firstTargetSide t) :
    B.firstTargetPos s < B.firstTargetPos t := by
  have hmono := B.firstArc_isCutPath.cut.mono_le hside.le
  rw [(B.firstArcCut_target hs).1, (B.firstArcCut_target ht).1] at hmono
  apply lt_of_le_of_ne hmono
  intro heq
  have hst : s = t := B.componentPlacement.firstPos_injective hs ht heq
  subst t
  exact (lt_irrefl _ hside)

theorem secondTargetPos_lt_of_side_lt
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    {s t : ℕ} (hs : s ∈ B.secondTarget) (ht : t ∈ B.secondTarget)
    (hside : B.secondTargetSide s < B.secondTargetSide t) :
    B.secondTargetPos s < B.secondTargetPos t := by
  have hmono := B.secondArc_isCutPath.cut.mono_le hside.le
  rw [(B.secondArcCut_target hs).1, (B.secondArcCut_target ht).1] at hmono
  apply lt_of_le_of_ne hmono
  intro heq
  have hst : s = t := B.componentPlacement.secondPos_injective hs ht heq
  subst t
  exact (lt_irrefl _ hside)

/-- Every inherited target strictly retained in a first-half gap survived the
half cut. -/
theorem firstGapArcSource_survives
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j) :
    B.componentPlacement.firstSurvives s := by
  have hsData := Finset.mem_filter.mp hs
  by_contra hnot
  have hsBroken : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives :=
    mem_brokenSet_iff.mpr ⟨hsData.1, hnot⟩
  apply HalfGap.not_mem_of_strict_between
    B.brokenAssignment.index.first j s hsBroken
  · intro e hprev
    let t := HalfEntry.entrySource B.brokenAssignment.index.first e
    have htBroken := HalfEntry.entrySource_mem
      B.brokenAssignment.index.first e
    have htTarget := (mem_brokenSet_iff.mp htBroken).1
    have hstart : B.firstGapStartSide j = B.firstTargetSide t + 1 := by
      simp only [firstGapStartSide]
      rw [hprev]
    apply B.firstTargetPos_lt_of_side_lt htTarget hsData.1
    dsimp [t] at hstart ⊢
    omega
  · intro e hnext
    let t := HalfEntry.entrySource B.brokenAssignment.index.first e
    have htBroken := HalfEntry.entrySource_mem
      B.brokenAssignment.index.first e
    have htTarget := (mem_brokenSet_iff.mp htBroken).1
    have hfinish : B.firstGapFinishSide j = B.firstTargetSide t := by
      simp only [firstGapFinishSide]
      rw [hnext]
    apply B.firstTargetPos_lt_of_side_lt hsData.1 htTarget
    dsimp [t] at hfinish ⊢
    omega

/-- Every inherited target strictly retained in a wrapped-half gap survived
the half cut. -/
theorem secondGapArcSource_survives
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j) :
    B.componentPlacement.secondSurvives s := by
  have hsData := Finset.mem_filter.mp hs
  by_contra hnot
  have hsBroken : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives :=
    mem_brokenSet_iff.mpr ⟨hsData.1, hnot⟩
  apply HalfGap.not_mem_of_strict_between
    B.brokenAssignment.index.second j s hsBroken
  · intro e hprev
    let t := HalfEntry.entrySource B.brokenAssignment.index.second e
    have htBroken := HalfEntry.entrySource_mem
      B.brokenAssignment.index.second e
    have htTarget := (mem_brokenSet_iff.mp htBroken).1
    have hstart : B.secondGapStartSide j = B.secondTargetSide t + 1 := by
      simp only [secondGapStartSide]
      rw [hprev]
    apply B.secondTargetPos_lt_of_side_lt htTarget hsData.1
    dsimp [t] at hstart ⊢
    omega
  · intro e hnext
    let t := HalfEntry.entrySource B.brokenAssignment.index.second e
    have htBroken := HalfEntry.entrySource_mem
      B.brokenAssignment.index.second e
    have htTarget := (mem_brokenSet_iff.mp htBroken).1
    have hfinish : B.secondGapFinishSide j = B.secondTargetSide t := by
      simp only [secondGapFinishSide]
      rw [hnext]
    apply B.secondTargetPos_lt_of_side_lt hsData.1 htTarget
    dsimp [t] at hfinish ⊢
    omega

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
