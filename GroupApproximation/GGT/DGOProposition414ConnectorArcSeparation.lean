import GroupApproximation.GGT.DGOProposition414ConnectorSeparationTransport

/-!
# Arc and opposite-connector opponents for connector targets

The inherited arc excludes both neighboring broken source letters. The two
connectors belong to distinct source components in that parent arc. These
facts reduce their separation to the same isolated-singleton argument.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- An anchored source does not connect to a distinct letter in the child arc. -/
theorem firstGap_not_connected_arc_of_source_anchor
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstTarget) {i r : ℕ}
    (hanchor : (vertex B.firstBase B.firstArc (B.firstTargetPos s))⁻¹ *
      vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j) i ∈ D.fam (P.label s))
    (hr : r < (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length)
    (hne : B.firstArcCut (B.firstGapStartSide j) + r ≠ B.firstTargetPos s)
    (hop : IsCompStart (P.label s) (B.firstGapCycle j) ((B.firstGapLeft j).length + r)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j) i
      ((B.firstGapLeft j).length + r) := by
  have hfinish := B.firstSeparation_arcCut_finish_le j
  have hr' : r < B.firstArcCut (B.firstGapFinishSide j) -
      B.firstArcCut (B.firstGapStartSide j) := by rwa [B.firstSeparation_arcBlock_length j] at hr
  have hm : B.firstArcCut (B.firstGapStartSide j) + r < B.firstArc.length := by omega
  obtain ⟨endPos, hcomp⟩ := hop
  have hcycle := hcomp.1.trans_le hcomp.2.1
  have hletter := (isCompOf_auxiliaryCycle_arc_iff (P.label s) (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)) (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j) (B.firstGapChordFinish j)) r hr hcycle).mp
      (hcomp.2.2.1 _ le_rfl hcomp.1 hcycle)
  rw [getElem_arcWord B.firstArc B.firstArcCut hfinish hr'] at hletter
  apply B.firstGap_not_connected_of_distinct_arc_letter j s hs hanchor hm le_rfl
    (Nat.le_succ _) hne hletter
  rw [B.firstSeparation_vertex_arc j hr'.le]
  have hvert : vertex B.firstBase B.firstWord (B.firstArcCut (B.firstGapStartSide j) + r) =
      vertex B.firstBase B.firstArc (B.firstArcCut (B.firstGapStartSide j) + r) := by
    calc
      _ = vertex B.firstBase (B.firstArc ++ revWord B.chord) (B.firstArcCut (B.firstGapStartSide j) + r) :=
        congrArg (fun word => vertex B.firstBase word (B.firstArcCut (B.firstGapStartSide j) + r)) B.firstWord_eq_append
      _ = _ := vertex_append_left _ _ _ hm.le
  rw [hvert, inv_mul_cancel]
  exact (D.fam (P.label s)).one_mem

/-- The two connector starts cannot lie in the same peripheral coset of a
common label, since their distinct sources are isolated in the parent arc. -/
theorem firstGapLeftRight_not_connected
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (p e : Fin B.brokenAssignment.index.first.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.first j = some p)
    (hn : HalfGap.nextEntry B.brokenAssignment.index.first j = some e)
    (hlabel : P.label (HalfEntry.entrySource B.brokenAssignment.index.first p) =
      P.label (HalfEntry.entrySource B.brokenAssignment.index.first e)) :
    ¬ Connected D.fam (P.label (HalfEntry.entrySource B.brokenAssignment.index.first p))
      (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j) 0
      ((B.firstGapLeft j).length + (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length) := by
  have hpTarget := (mem_brokenSet_iff.mp (HalfEntry.entrySource_mem B.brokenAssignment.index.first p)).1
  have heTarget := (mem_brokenSet_iff.mp (HalfEntry.entrySource_mem B.brokenAssignment.index.first e)).1
  have heComp := B.firstArc_targetComponent heTarget
  have heLt := heComp.1.trans_le heComp.2.1
  have heLetter := heComp.2.2.1 _ le_rfl heComp.1 heLt
  rw [← hlabel] at heLetter
  have hne : B.firstTargetPos (HalfEntry.entrySource B.brokenAssignment.index.first e) ≠
      B.firstTargetPos (HalfEntry.entrySource B.brokenAssignment.index.first p) := by
    intro heq
    exact HalfGap.entrySource_ne_of_adjacent B.brokenAssignment.index.first j hp hn
      (B.componentPlacement.firstPos_injective heTarget hpTarget heq).symm
  apply B.firstGap_not_connected_of_distinct_arc_letter j _ hpTarget
    (B.firstGapLeft_sourceArc_mem j p hp) heLt le_rfl (Nat.le_succ _) hne heLetter
  rw [B.firstGapRight_sourceArc_vertex j e hn, inv_mul_cancel]
  exact (D.fam _).one_mem

/-- An anchored source does not connect to a distinct letter in the child arc. -/
theorem secondGap_not_connected_arc_of_source_anchor
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondTarget) {i r : ℕ}
    (hanchor : (vertex B.secondBase B.secondArc (B.secondTargetPos s))⁻¹ *
      vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j) i ∈ D.fam (P.label s))
    (hr : r < (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length)
    (hne : B.secondArcCut (B.secondGapStartSide j) + r ≠ B.secondTargetPos s)
    (hop : IsCompStart (P.label s) (B.secondGapCycle j) ((B.secondGapLeft j).length + r)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j) i
      ((B.secondGapLeft j).length + r) := by
  have hfinish := B.secondSeparation_arcCut_finish_le j
  have hr' : r < B.secondArcCut (B.secondGapFinishSide j) -
      B.secondArcCut (B.secondGapStartSide j) := by rwa [B.secondSeparation_arcBlock_length j] at hr
  have hm : B.secondArcCut (B.secondGapStartSide j) + r < B.secondArc.length := by omega
  obtain ⟨endPos, hcomp⟩ := hop
  have hcycle := hcomp.1.trans_le hcomp.2.1
  have hletter := (isCompOf_auxiliaryCycle_arc_iff (P.label s) (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)) (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j) (B.secondGapChordFinish j)) r hr hcycle).mp
      (hcomp.2.2.1 _ le_rfl hcomp.1 hcycle)
  rw [getElem_arcWord B.secondArc B.secondArcCut hfinish hr'] at hletter
  apply B.secondGap_not_connected_of_distinct_arc_letter j s hs hanchor hm le_rfl
    (Nat.le_succ _) hne hletter
  rw [B.secondSeparation_vertex_arc j hr'.le]
  have hvert : vertex B.secondBase B.secondWord (B.secondArcCut (B.secondGapStartSide j) + r) =
      vertex B.secondBase B.secondArc (B.secondArcCut (B.secondGapStartSide j) + r) := by
    calc
      _ = vertex B.secondBase (B.secondArc ++ B.chord) (B.secondArcCut (B.secondGapStartSide j) + r) :=
        congrArg (fun word => vertex B.secondBase word (B.secondArcCut (B.secondGapStartSide j) + r)) B.secondWord_eq_append
      _ = _ := vertex_append_left _ _ _ hm.le
  rw [hvert, inv_mul_cancel]
  exact (D.fam (P.label s)).one_mem

/-- The two connector starts cannot lie in the same peripheral coset of a
common label, since their distinct sources are isolated in the parent arc. -/
theorem secondGapLeftRight_not_connected
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (p e : Fin B.brokenAssignment.index.second.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.second j = some p)
    (hn : HalfGap.nextEntry B.brokenAssignment.index.second j = some e)
    (hlabel : P.label (HalfEntry.entrySource B.brokenAssignment.index.second p) =
      P.label (HalfEntry.entrySource B.brokenAssignment.index.second e)) :
    ¬ Connected D.fam (P.label (HalfEntry.entrySource B.brokenAssignment.index.second p))
      (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j) 0
      ((B.secondGapLeft j).length + (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length) := by
  have hpTarget := (mem_brokenSet_iff.mp (HalfEntry.entrySource_mem B.brokenAssignment.index.second p)).1
  have heTarget := (mem_brokenSet_iff.mp (HalfEntry.entrySource_mem B.brokenAssignment.index.second e)).1
  have heComp := B.secondArc_targetComponent heTarget
  have heLt := heComp.1.trans_le heComp.2.1
  have heLetter := heComp.2.2.1 _ le_rfl heComp.1 heLt
  rw [← hlabel] at heLetter
  have hne : B.secondTargetPos (HalfEntry.entrySource B.brokenAssignment.index.second e) ≠
      B.secondTargetPos (HalfEntry.entrySource B.brokenAssignment.index.second p) := by
    intro heq
    exact HalfGap.entrySource_ne_of_adjacent B.brokenAssignment.index.second j hp hn
      (B.componentPlacement.secondPos_injective heTarget hpTarget heq).symm
  apply B.secondGap_not_connected_of_distinct_arc_letter j _ hpTarget
    (B.secondGapLeft_sourceArc_mem j p hp) heLt le_rfl (Nat.le_succ _) hne heLetter
  rw [B.secondGapRight_sourceArc_vertex j e hn, inv_mul_cancel]
  exact (D.fam _).one_mem

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGap_not_connected_arc_of_source_anchor

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapLeftRight_not_connected

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGap_not_connected_arc_of_source_anchor

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapLeftRight_not_connected
