import GroupApproximation.GGT.DGOProposition414FirstChargedArcSeparation

/-!
# Separating charged first-gap targets from the two connectors

Each nonempty connector meets an endpoint of its broken first-half source.
A charged opposite-half source is isolated from every same-label first-arc
letter in the parent polygon, so neither connector can connect to it.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- A charged opposite-half target cannot connect to the right connector of its gap. -/
theorem firstGapChordSource_not_connected_right
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapChordSources j) {r : ℕ}
    (hr : r < (B.firstGapRight j).length)
    (hop : IsCompStart (P.label s) (B.firstGapCycle j)
      ((B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length + r)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
      (B.firstGapCut j (B.firstGapChordTargetIndex j (B.brokenAssignment.second.partner s)))
      ((B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length + r) := by
  classical
  have hlen := B.firstGapRight_length_le_one j
  have hr0 : r = 0 := by omega
  subst r
  cases hn : HalfGap.nextEntry B.brokenAssignment.index.first j with
  | none =>
    have : B.firstGapRight j = [] := by simp only [firstGapRight]; rw [hn]
    simp [this] at hr
  | some e =>
    let t := HalfEntry.entrySource B.brokenAssignment.index.first e
    have ht := (mem_brokenSet_iff.mp (HalfEntry.entrySource_mem B.brokenAssignment.index.first e)).1
    have hfinish : B.firstGapFinishSide j = B.firstTargetSide t := by
      simp only [firstGapFinishSide]; rw [hn]
    obtain ⟨endPos, hcomp⟩ := hop
    have hcycle := hcomp.1.trans_le hcomp.2.1
    have hletter := hcomp.2.2.1 _ le_rfl hcomp.1 hcycle
    have hown := B.firstGap_rightConnector_isCompOf j e hn 0 hr hcycle
    rw [B.firstGapLocalLabel_rightConnector j e hn 0 hr] at hown
    have hlabel : P.label s = P.label t := eq_of_isCompOf_of_isCompOf hletter hown
    have htComp := B.firstArc_targetComponent ht
    have htLt := htComp.1.trans_le htComp.2.1
    have htLetter := htComp.2.2.1 _ le_rfl htComp.1 htLt
    rw [← hlabel] at htLetter
    apply B.firstGapChordSource_not_connected_of_arc_anchor j s hs htLt le_rfl
      (Nat.le_succ _) htLetter
    rw [Nat.add_zero, B.firstSeparation_arcBlock_length j,
      B.firstSeparation_vertex_arc j le_rfl,
      Nat.add_sub_of_le (B.firstSeparation_arcCut_mono j), hfinish,
      (B.firstArcCut_target ht).1]
    have hvert : vertex B.firstBase B.firstWord (B.firstTargetPos t) =
        vertex B.firstBase B.firstArc (B.firstTargetPos t) := by
      calc
        _ = vertex B.firstBase (B.firstArc ++ revWord B.chord) (B.firstTargetPos t) :=
          congrArg (fun word => vertex B.firstBase word (B.firstTargetPos t)) B.firstWord_eq_append
        _ = _ := vertex_append_left _ _ _ htLt.le
    rw [hvert, inv_mul_cancel]
    exact (D.fam (P.label s)).one_mem

/-- A charged opposite-half target cannot connect to the reversed left connector. -/
theorem firstGapChordSource_not_connected_left
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapChordSources j) {q : ℕ}
    (hq : q < (B.firstGapLeft j).length)
    (hop : IsCompStart (P.label s) (B.firstGapCycle j) q) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
      (B.firstGapCut j (B.firstGapChordTargetIndex j (B.brokenAssignment.second.partner s))) q := by
  classical
  have hlen := B.firstGapLeft_length_le_one j
  have hq0 : q = 0 := by omega
  subst q
  cases hp : HalfGap.previousEntry B.brokenAssignment.index.first j with
  | none =>
    have : B.firstGapLeft j = [] := by simp only [firstGapLeft]; rw [hp]
    simp [this] at hq
  | some e =>
    let t := HalfEntry.entrySource B.brokenAssignment.index.first e
    have ht := (mem_brokenSet_iff.mp (HalfEntry.entrySource_mem B.brokenAssignment.index.first e)).1
    have hstart : B.firstGapStartSide j = B.firstTargetSide t + 1 := by
      simp only [firstGapStartSide]; rw [hp]
    obtain ⟨endPos, hcomp⟩ := hop
    have hcycle := hcomp.1.trans_le hcomp.2.1
    have hletter := hcomp.2.2.1 _ le_rfl hcomp.1 hcycle
    have hown := B.firstGap_leftConnector_isCompOf j e hp 0 hq hcycle
    rw [B.firstGapLocalLabel_leftConnector j e hp 0 hq] at hown
    have hlabel : P.label s = P.label t := eq_of_isCompOf_of_isCompOf hletter hown
    have hleft := listVal_mem_fam_of_isCompOf D (P.label t) (B.firstGapLeft j)
      (B.firstGapLeft_letters j) (B.firstGapLeft_label j e hp)
    have hreverse : RelLetter.listVal (revWord (B.firstGapLeft j)) ∈ D.fam (P.label s) := by
      rw [listVal_revWord, hlabel]
      exact (D.fam (P.label t)).inv_mem hleft
    have hlanding : vertex B.firstBase B.chord (B.firstGapChordFinish j) *
        RelLetter.listVal (revWord (B.firstGapLeft j)) =
        vertex B.firstBase B.firstArc (B.firstTargetPos t + 1) := by
      rw [B.firstGap_arcBase j, hstart, (B.firstArcCut_target ht).2]
    have htComp := B.firstArc_targetComponent ht
    have htLt := htComp.1.trans_le htComp.2.1
    have htLetter := htComp.2.2.1 _ le_rfl htComp.1 htLt
    rw [← hlabel] at htLetter
    apply B.firstGapChordSource_not_connected_of_arc_anchor j s hs htLt
      (Nat.le_succ _) le_rfl htLetter
    rw [vertex_zero, ← hlanding, inv_mul_cancel_left]
    exact hreverse

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapChordSource_not_connected_right
#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapChordSource_not_connected_left
