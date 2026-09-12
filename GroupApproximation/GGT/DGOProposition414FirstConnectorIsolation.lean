import GroupApproximation.GGT.DGOProposition414ConnectorArcSeparation
import GroupApproximation.GGT.DGOProposition414ConnectorCuts
import GroupApproximation.GGT.DGOProposition414AdjacentPartnerExclusion
import GroupApproximation.GGT.DGOProposition414CycleBlocks

/-!
# Full connector-target isolation in the first-half auxiliary cycles

Arc opponents contradict isolation of the broken source in its inherited arc;
the other connector belongs to a distinct broken source; chord opponents
contradict geodesicity since the source's partner edge is omitted by the child.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- Every nonempty left connector is isolated in the entire child cycle. -/
theorem firstGapLeft_cycleIsolated
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (p : Fin B.brokenAssignment.index.first.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.first j = some p)
    (hleft : 0 < (B.firstGapLeft j).length) :
    IsIsolated D.fam (P.label (HalfEntry.entrySource B.brokenAssignment.index.first p))
      (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j) 0 := by
  have hpBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.first p
  have hpTarget := (mem_brokenSet_iff.mp hpBroken).1
  have hcomp := B.firstGapLeftComponentField j 0 hleft
  rw [B.firstGapLocalLabel_leftConnector j p hp 0 hleft,
    B.firstGapCut_left j (Nat.zero_le _), B.firstGapCut_left j (Nat.succ_le_of_lt hleft)] at hcomp
  refine ⟨⟨1, hcomp⟩, ?_⟩
  intro q hne hop
  have hq : q < (B.firstGapCycle j).length := hop.choose_spec.1.trans_le hop.choose_spec.2.1
  rcases auxiliaryCycleWord_index_cases (B.firstGapLeft j) (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j))
      (B.firstGapRight j) (orientedSegment B.chord (B.firstGapChordStart j) (B.firstGapChordFinish j)) hq with
    hqleft | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · have hlen := B.firstGapLeft_length_le_one j
    exact False.elim (hne (by omega))
  · apply B.firstGap_not_connected_arc_of_source_anchor j _ hpTarget
      (B.firstGapLeft_sourceArc_mem j p hp) hr ?_ hop
    have hstart : B.firstGapStartSide j =
        B.firstTargetSide (HalfEntry.entrySource B.brokenAssignment.index.first p) + 1 := by
      simp only [firstGapStartSide]; rw [hp]
    rw [hstart, (B.firstArcCut_target hpTarget).2]
    omega
  · have hlen := B.firstGapRight_length_le_one j
    have hr0 : r = 0 := by omega
    subst r
    simp only [Nat.add_zero] at hop ⊢
    cases hn : HalfGap.nextEntry B.brokenAssignment.index.first j with
    | none =>
      have hnil : B.firstGapRight j = [] := by simp only [firstGapRight]; rw [hn]
      simp [hnil] at hr
    | some e =>
      have hc := hop.choose_spec
      have hcycle := hc.1.trans_le hc.2.1
      have hletter := hc.2.2.1 _ le_rfl hc.1 hcycle
      have hown := B.firstGap_rightConnector_isCompOf j e hn 0 hr hcycle
      rw [B.firstGapLocalLabel_rightConnector j e hn 0 hr] at hown
      have hlabel := eq_of_isCompOf_of_isCompOf hletter hown
      exact B.firstGapLeftRight_not_connected j p e hp hn hlabel
  · exact B.firstGap_not_connected_chord_of_source_anchor j _ hpBroken
      (B.firstGapLeft_sourceArc_mem j p hp) (B.firstGapChord_not_edge_previous j p hp) hr hop

/-- Every nonempty right connector is isolated in the entire child cycle. -/
theorem firstGapRight_cycleIsolated
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (hn : HalfGap.nextEntry B.brokenAssignment.index.first j = some e)
    (hright : 0 < (B.firstGapRight j).length) :
    IsIsolated D.fam (P.label (HalfEntry.entrySource B.brokenAssignment.index.first e))
      (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
      ((B.firstGapLeft j).length + (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length) := by
  have heBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
  have heTarget := (mem_brokenSet_iff.mp heBroken).1
  have hcomp := B.firstGap_rightComponent j 0 hright
  have hcut0 := B.firstGapCut_right j (r := 0) (Nat.zero_le _)
  have hcut1 := B.firstGapCut_right j (r := 1) (Nat.succ_le_of_lt hright)
  have hlabel := B.firstGapLocalLabel_rightConnector j e hn 0 hright
  simp only [Nat.add_zero] at hcomp hcut0 hlabel
  rw [hcut0, hcut1, hlabel] at hcomp
  have hanchor : (vertex B.firstBase B.firstArc
      (B.firstTargetPos (HalfEntry.entrySource B.brokenAssignment.index.first e)))⁻¹ *
      vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
        ((B.firstGapLeft j).length + (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length) ∈
      D.fam (P.label (HalfEntry.entrySource B.brokenAssignment.index.first e)) := by
    rw [B.firstGapRight_sourceArc_vertex j e hn, inv_mul_cancel]
    exact (D.fam _).one_mem
  refine ⟨⟨_, hcomp⟩, ?_⟩
  intro q hne hop
  have hq : q < (B.firstGapCycle j).length := hop.choose_spec.1.trans_le hop.choose_spec.2.1
  rcases auxiliaryCycleWord_index_cases (B.firstGapLeft j) (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j))
      (B.firstGapRight j) (orientedSegment B.chord (B.firstGapChordStart j) (B.firstGapChordFinish j)) hq with
    hqleft | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · have hlen := B.firstGapLeft_length_le_one j
    have hq0 : q = 0 := by omega
    subst q
    cases hp : HalfGap.previousEntry B.brokenAssignment.index.first j with
    | none =>
      have hnil : B.firstGapLeft j = [] := by simp only [firstGapLeft]; rw [hp]
      simp [hnil] at hqleft
    | some p =>
      have hc := hop.choose_spec
      have hcycle := hc.1.trans_le hc.2.1
      have hletter := hc.2.2.1 _ le_rfl hc.1 hcycle
      have hown := B.firstGap_leftConnector_isCompOf j p hp 0 hqleft hcycle
      rw [B.firstGapLocalLabel_leftConnector j p hp 0 hqleft] at hown
      have hlabels := eq_of_isCompOf_of_isCompOf hletter hown
      have hnot := B.firstGapLeftRight_not_connected j p e hp hn hlabels.symm
      rw [← hlabels] at hnot
      exact fun hc => hnot (connected_symm hc)
  · apply B.firstGap_not_connected_arc_of_source_anchor j _ heTarget hanchor hr ?_ hop
    have hfinish : B.firstGapFinishSide j =
        B.firstTargetSide (HalfEntry.entrySource B.brokenAssignment.index.first e) := by
      simp only [firstGapFinishSide]; rw [hn]
    rw [B.firstSeparation_arcBlock_length j, hfinish, (B.firstArcCut_target heTarget).1] at hr
    omega
  · have hlen := B.firstGapRight_length_le_one j
    exact False.elim (hne (by omega))
  · exact B.firstGap_not_connected_chord_of_source_anchor j _ heBroken hanchor
      (B.firstGapChord_not_edge_next j e hn) hr hop

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapLeft_cycleIsolated
#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapRight_cycleIsolated
