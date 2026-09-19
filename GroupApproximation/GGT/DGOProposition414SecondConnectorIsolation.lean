import GroupApproximation.GGT.DGOProposition414ConnectorArcSeparation
import GroupApproximation.GGT.DGOProposition414ConnectorCuts
import GroupApproximation.GGT.DGOProposition414AdjacentPartnerExclusion
import GroupApproximation.GGT.DGOProposition414CycleBlocks

/-!
# Full connector-target isolation in the second-half auxiliary cycles

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
theorem secondGapLeft_cycleIsolated
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (p : Fin B.brokenAssignment.index.second.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.second j = some p)
    (hleft : 0 < (B.secondGapLeft j).length) :
    IsIsolated D.fam (P.label (HalfEntry.entrySource B.brokenAssignment.index.second p))
      (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j) 0 := by
  have hpBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.second p
  have hpTarget := (mem_brokenSet_iff.mp hpBroken).1
  have hcomp := B.secondGapLeftComponentField j 0 hleft
  rw [B.secondGapLocalLabel_leftConnector j p hp 0 hleft,
    B.secondGapCut_left j (Nat.zero_le _), B.secondGapCut_left j (Nat.succ_le_of_lt hleft)] at hcomp
  refine ⟨⟨1, hcomp⟩, ?_⟩
  intro q hne hop
  have hq : q < (B.secondGapCycle j).length := hop.choose_spec.1.trans_le hop.choose_spec.2.1
  rcases auxiliaryCycleWord_index_cases (B.secondGapLeft j) (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j))
      (B.secondGapRight j) (orientedSegment B.chord (B.secondGapChordStart j) (B.secondGapChordFinish j)) hq with
    hqleft | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · have hlen := B.secondGapLeft_length_le_one j
    exact False.elim (hne (by omega))
  · apply B.secondGap_not_connected_arc_of_source_anchor j _ hpTarget
      (B.secondGapLeft_sourceArc_mem j p hp) hr ?_ hop
    have hstart : B.secondGapStartSide j =
        B.secondTargetSide (HalfEntry.entrySource B.brokenAssignment.index.second p) + 1 := by
      simp only [secondGapStartSide]; rw [hp]
    rw [hstart, (B.secondArcCut_target hpTarget).2]
    omega
  · have hlen := B.secondGapRight_length_le_one j
    have hr0 : r = 0 := by omega
    subst r
    simp only [Nat.add_zero] at hop ⊢
    cases hn : HalfGap.nextEntry B.brokenAssignment.index.second j with
    | none =>
      have hnil : B.secondGapRight j = [] := by simp only [secondGapRight]; rw [hn]
      simp [hnil] at hr
    | some e =>
      have hc := hop.choose_spec
      have hcycle := hc.1.trans_le hc.2.1
      have hletter := hc.2.2.1 _ le_rfl hc.1 hcycle
      have hown := B.secondGap_rightConnector_isCompOf j e hn 0 hr hcycle
      rw [B.secondGapLocalLabel_rightConnector j e hn 0 hr] at hown
      have hlabel := eq_of_isCompOf_of_isCompOf hletter hown
      exact B.secondGapLeftRight_not_connected j p e hp hn hlabel
  · exact B.secondGap_not_connected_chord_of_source_anchor j _ hpBroken
      (B.secondGapLeft_sourceArc_mem j p hp) (B.secondGapChord_not_edge_previous j p hp) hr hop

/-- Every nonempty right connector is isolated in the entire child cycle. -/
theorem secondGapRight_cycleIsolated
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (hn : HalfGap.nextEntry B.brokenAssignment.index.second j = some e)
    (hright : 0 < (B.secondGapRight j).length) :
    IsIsolated D.fam (P.label (HalfEntry.entrySource B.brokenAssignment.index.second e))
      (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
      ((B.secondGapLeft j).length + (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length) := by
  have heBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.second e
  have heTarget := (mem_brokenSet_iff.mp heBroken).1
  have hcomp := B.secondGap_rightComponent j 0 hright
  have hcut0 := B.secondGapCut_right j (r := 0) (Nat.zero_le _)
  have hcut1 := B.secondGapCut_right j (r := 1) (Nat.succ_le_of_lt hright)
  have hlabel := B.secondGapLocalLabel_rightConnector j e hn 0 hright
  simp only [Nat.add_zero] at hcomp hcut0 hlabel
  rw [hcut0, hcut1, hlabel] at hcomp
  have hanchor : (vertex B.secondBase B.secondArc
      (B.secondTargetPos (HalfEntry.entrySource B.brokenAssignment.index.second e)))⁻¹ *
      vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
        ((B.secondGapLeft j).length + (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length) ∈
      D.fam (P.label (HalfEntry.entrySource B.brokenAssignment.index.second e)) := by
    rw [B.secondGapRight_sourceArc_vertex j e hn, inv_mul_cancel]
    exact (D.fam _).one_mem
  refine ⟨⟨_, hcomp⟩, ?_⟩
  intro q hne hop
  have hq : q < (B.secondGapCycle j).length := hop.choose_spec.1.trans_le hop.choose_spec.2.1
  rcases auxiliaryCycleWord_index_cases (B.secondGapLeft j) (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j))
      (B.secondGapRight j) (orientedSegment B.chord (B.secondGapChordStart j) (B.secondGapChordFinish j)) hq with
    hqleft | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · have hlen := B.secondGapLeft_length_le_one j
    have hq0 : q = 0 := by omega
    subst q
    cases hp : HalfGap.previousEntry B.brokenAssignment.index.second j with
    | none =>
      have hnil : B.secondGapLeft j = [] := by simp only [secondGapLeft]; rw [hp]
      simp [hnil] at hqleft
    | some p =>
      have hc := hop.choose_spec
      have hcycle := hc.1.trans_le hc.2.1
      have hletter := hc.2.2.1 _ le_rfl hc.1 hcycle
      have hown := B.secondGap_leftConnector_isCompOf j p hp 0 hqleft hcycle
      rw [B.secondGapLocalLabel_leftConnector j p hp 0 hqleft] at hown
      have hlabels := eq_of_isCompOf_of_isCompOf hletter hown
      have hnot := B.secondGapLeftRight_not_connected j p e hp hn hlabels.symm
      rw [← hlabels] at hnot
      exact fun hc => hnot (connected_symm hc)
  · apply B.secondGap_not_connected_arc_of_source_anchor j _ heTarget hanchor hr ?_ hop
    have hfinish : B.secondGapFinishSide j =
        B.secondTargetSide (HalfEntry.entrySource B.brokenAssignment.index.second e) := by
      simp only [secondGapFinishSide]; rw [hn]
    rw [B.secondSeparation_arcBlock_length j, hfinish, (B.secondArcCut_target heTarget).1] at hr
    omega
  · have hlen := B.secondGapRight_length_le_one j
    exact False.elim (hne (by omega))
  · exact B.secondGap_not_connected_chord_of_source_anchor j _ heBroken hanchor
      (B.secondGapChord_not_edge_next j e hn) hr hop

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapLeft_cycleIsolated
#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapRight_cycleIsolated
