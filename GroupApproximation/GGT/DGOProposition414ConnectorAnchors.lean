import GroupApproximation.GGT.DGOProposition414FirstSeparationTransport
import GroupApproximation.GGT.DGOProposition414ChordArcSeamProofWrapped

/-!
# Source and partner cosets of the connector targets

The right connector starts at its broken source's initial vertex. The reversed
left connector ends at its broken source's terminal vertex. These dictionaries
keep the source in the inherited arc, where it remains isolated, and connect
that source to the global chord partner in either orientation of the half word.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- A distinguished first-half source has the same vertex in the arc and half word. -/
theorem firstTarget_arc_vertex
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ B.firstTarget) :
    vertex B.firstBase B.firstWord (B.firstTargetPos s) =
      vertex B.firstBase B.firstArc (B.firstTargetPos s) := by
  rw [B.firstWord_eq_append]
  exact vertex_append_left _ _ _ (by rw [B.firstArc_length_eq]; exact (B.firstTargetPos_lt hs).le)

/-- A broken first-half source is connected to the initial vertex of its
partner edge on the forward global chord. -/
theorem firstBrokenSource_arc_partner_mem
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    (vertex B.firstBase B.firstArc (B.firstTargetPos s))⁻¹ *
      vertex B.firstBase B.chord (B.brokenAssignment.first.partner s) ∈ D.fam (P.label s) := by
  have hsTarget := (mem_brokenSet_iff.mp hs).1
  have hA := B.brokenAssignment.first.partner_connected s hs
  change (vertex B.firstBase B.firstWord (B.firstTargetPos s))⁻¹ *
    vertex B.firstBase B.firstWord (B.firstChordPos (B.brokenAssignment.first.partner s)) ∈ D.fam (P.label s) at hA
  rw [B.firstBrokenConnectors_partnerStart_vertex s hs, B.firstTarget_arc_vertex s hsTarget] at hA
  have hspan := span_mem_fam_of_isComp D B.firstBase B.chord_geodesic.1
    (B.firstPartner_chord_isComp s hs)
  convert (D.fam (P.label s)).mul_mem hA ((D.fam (P.label s)).inv_mem hspan) using 1
  group

/-- The right-connector initial vertex is the following source's arc vertex. -/
theorem firstGapRight_sourceArc_vertex
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (hn : HalfGap.nextEntry B.brokenAssignment.index.first j = some e) :
    vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
      ((B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length) =
      vertex B.firstBase B.firstArc
        (B.firstTargetPos (HalfEntry.entrySource B.brokenAssignment.index.first e)) := by
  have ht := (mem_brokenSet_iff.mp (HalfEntry.entrySource_mem B.brokenAssignment.index.first e)).1
  have hfinish : B.firstGapFinishSide j =
      B.firstTargetSide (HalfEntry.entrySource B.brokenAssignment.index.first e) := by
    simp only [firstGapFinishSide]; rw [hn]
  rw [B.firstSeparation_arcBlock_length j, B.firstSeparation_vertex_arc j le_rfl,
    Nat.add_sub_of_le (B.firstSeparation_arcCut_mono j), hfinish,
    (B.firstArcCut_target ht).1, B.firstTarget_arc_vertex _ ht]

/-- The left-connector initial vertex lies in the preceding source's arc coset. -/
theorem firstGapLeft_sourceArc_mem
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.first j = some e) :
    (vertex B.firstBase B.firstArc
      (B.firstTargetPos (HalfEntry.entrySource B.brokenAssignment.index.first e)))⁻¹ *
      vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j) 0 ∈
      D.fam (P.label (HalfEntry.entrySource B.brokenAssignment.index.first e)) := by
  let t := HalfEntry.entrySource B.brokenAssignment.index.first e
  have ht := (mem_brokenSet_iff.mp (HalfEntry.entrySource_mem B.brokenAssignment.index.first e)).1
  have hstart : B.firstGapStartSide j = B.firstTargetSide t + 1 := by
    simp only [firstGapStartSide]; rw [hp]
  have hleft := listVal_mem_fam_of_isCompOf D (P.label t) (B.firstGapLeft j)
    (B.firstGapLeft_letters j) (B.firstGapLeft_label j e hp)
  have hreverse : RelLetter.listVal (revWord (B.firstGapLeft j)) ∈ D.fam (P.label t) := by
    rw [listVal_revWord]
    exact (D.fam (P.label t)).inv_mem hleft
  have hlanding : vertex B.firstBase B.chord (B.firstGapChordFinish j) *
      RelLetter.listVal (revWord (B.firstGapLeft j)) =
      vertex B.firstBase B.firstArc (B.firstTargetPos t + 1) := by
    rw [B.firstGap_arcBase j, hstart, (B.firstArcCut_target ht).2]
  have hspan := span_mem_fam_of_isComp D B.firstBase B.firstArc_isCutPath.letters
    (B.firstArc_targetComponent ht)
  rw [vertex_zero]
  convert (D.fam (P.label t)).mul_mem hspan ((D.fam (P.label t)).inv_mem hreverse) using 1
  rw [← hlanding]
  group

/-- A distinguished second-half source has the same vertex in the arc and half word. -/
theorem secondTarget_arc_vertex
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ B.secondTarget) :
    vertex B.secondBase B.secondWord (B.secondTargetPos s) =
      vertex B.secondBase B.secondArc (B.secondTargetPos s) := by
  rw [B.secondWord_eq_append]
  exact vertex_append_left _ _ _ (by rw [B.secondArc_length_eq]; exact (B.secondTargetPos_lt hs).le)

/-- A broken second-half source is connected to the initial vertex of its
partner edge on the forward global chord. -/
theorem secondBrokenSource_arc_partner_mem
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    (vertex B.secondBase B.secondArc (B.secondTargetPos s))⁻¹ *
      vertex B.firstBase B.chord (B.brokenAssignment.second.partner s) ∈ D.fam (P.label s) := by
  have hsTarget := (mem_brokenSet_iff.mp hs).1
  have hA := B.brokenAssignment.second.partner_connected s hs
  change (vertex B.secondBase B.secondWord (B.secondTargetPos s))⁻¹ *
    vertex B.secondBase B.secondWord (B.secondChordPos (B.brokenAssignment.second.partner s)) ∈ D.fam (P.label s) at hA
  rw [B.secondBrokenConnectors_partnerStart_vertex s hs, B.secondTarget_arc_vertex s hsTarget] at hA
  exact hA

/-- The right-connector initial vertex is the following source's arc vertex. -/
theorem secondGapRight_sourceArc_vertex
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (hn : HalfGap.nextEntry B.brokenAssignment.index.second j = some e) :
    vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
      ((B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length) =
      vertex B.secondBase B.secondArc
        (B.secondTargetPos (HalfEntry.entrySource B.brokenAssignment.index.second e)) := by
  have ht := (mem_brokenSet_iff.mp (HalfEntry.entrySource_mem B.brokenAssignment.index.second e)).1
  have hfinish : B.secondGapFinishSide j =
      B.secondTargetSide (HalfEntry.entrySource B.brokenAssignment.index.second e) := by
    simp only [secondGapFinishSide]; rw [hn]
  rw [B.secondSeparation_arcBlock_length j, B.secondSeparation_vertex_arc j le_rfl,
    Nat.add_sub_of_le (B.secondSeparation_arcCut_mono j), hfinish,
    (B.secondArcCut_target ht).1, B.secondTarget_arc_vertex _ ht]

/-- The left-connector initial vertex lies in the preceding source's arc coset. -/
theorem secondGapLeft_sourceArc_mem
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.second j = some e) :
    (vertex B.secondBase B.secondArc
      (B.secondTargetPos (HalfEntry.entrySource B.brokenAssignment.index.second e)))⁻¹ *
      vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j) 0 ∈
      D.fam (P.label (HalfEntry.entrySource B.brokenAssignment.index.second e)) := by
  let t := HalfEntry.entrySource B.brokenAssignment.index.second e
  have ht := (mem_brokenSet_iff.mp (HalfEntry.entrySource_mem B.brokenAssignment.index.second e)).1
  have hstart : B.secondGapStartSide j = B.secondTargetSide t + 1 := by
    simp only [secondGapStartSide]; rw [hp]
  have hleft := listVal_mem_fam_of_isCompOf D (P.label t) (B.secondGapLeft j)
    (B.secondGapLeft_letters j) (B.secondGapLeft_label j e hp)
  have hreverse : RelLetter.listVal (revWord (B.secondGapLeft j)) ∈ D.fam (P.label t) := by
    rw [listVal_revWord]
    exact (D.fam (P.label t)).inv_mem hleft
  have hlanding : vertex B.firstBase B.chord (B.secondGapChordFinish j) *
      RelLetter.listVal (revWord (B.secondGapLeft j)) =
      vertex B.secondBase B.secondArc (B.secondTargetPos t + 1) := by
    rw [B.secondGap_arcBase j, hstart, (B.secondArcCut_target ht).2]
  have hspan := span_mem_fam_of_isComp D B.secondBase B.secondArc_isCutPath.letters
    (B.secondArc_targetComponent ht)
  rw [vertex_zero]
  convert (D.fam (P.label t)).mul_mem hspan ((D.fam (P.label t)).inv_mem hreverse) using 1
  rw [← hlanding]
  group

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstTarget_arc_vertex

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstBrokenSource_arc_partner_mem

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapRight_sourceArc_vertex

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapLeft_sourceArc_mem

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondTarget_arc_vertex

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondBrokenSource_arc_partner_mem

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapRight_sourceArc_vertex

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapLeft_sourceArc_mem
