import GroupApproximation.GGT.DGOProposition414SecondChargedArcSeparation

/-!
# Separating charged wrapped-gap targets from the two connectors

Each nonempty connector meets an endpoint of its broken second-half source.
A charged opposite-half source is isolated from every same-label second-arc
letter in the parent polygon, so neither connector can connect to it.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- A charged opposite-half target cannot connect to the right connector of its gap. -/
theorem secondGapChordSource_not_connected_right
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapChordSources j) {r : ℕ}
    (hr : r < (B.secondGapRight j).length)
    (hop : IsCompStart (P.label s) (B.secondGapCycle j)
      ((B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length + r)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
      (B.secondGapCut j (B.secondGapChordTargetIndex j (B.brokenAssignment.first.partner s)))
      ((B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length + r) := by
  classical
  have hlen := B.secondGapRight_length_le_one j
  have hr0 : r = 0 := by omega
  subst r
  cases hn : HalfGap.nextEntry B.brokenAssignment.index.second j with
  | none =>
    have : B.secondGapRight j = [] := by simp only [secondGapRight]; rw [hn]
    simp [this] at hr
  | some e =>
    let t := HalfEntry.entrySource B.brokenAssignment.index.second e
    have ht := (mem_brokenSet_iff.mp (HalfEntry.entrySource_mem B.brokenAssignment.index.second e)).1
    have hfinish : B.secondGapFinishSide j = B.secondTargetSide t := by
      simp only [secondGapFinishSide]; rw [hn]
    obtain ⟨endPos, hcomp⟩ := hop
    have hcycle := hcomp.1.trans_le hcomp.2.1
    have hletter := hcomp.2.2.1 _ le_rfl hcomp.1 hcycle
    have hown := B.secondGap_rightConnector_isCompOf j e hn 0 hr hcycle
    rw [B.secondGapLocalLabel_rightConnector j e hn 0 hr] at hown
    have hlabel : P.label s = P.label t := eq_of_isCompOf_of_isCompOf hletter hown
    have htComp := B.secondArc_targetComponent ht
    have htLt := htComp.1.trans_le htComp.2.1
    have htLetter := htComp.2.2.1 _ le_rfl htComp.1 htLt
    rw [← hlabel] at htLetter
    apply B.secondGapChordSource_not_connected_of_arc_anchor j s hs htLt le_rfl
      (Nat.le_succ _) htLetter
    rw [Nat.add_zero, B.secondSeparation_arcBlock_length j,
      B.secondSeparation_vertex_arc j le_rfl,
      Nat.add_sub_of_le (B.secondSeparation_arcCut_mono j), hfinish,
      (B.secondArcCut_target ht).1]
    have hvert : vertex B.secondBase B.secondWord (B.secondTargetPos t) =
        vertex B.secondBase B.secondArc (B.secondTargetPos t) := by
      calc
        _ = vertex B.secondBase (B.secondArc ++ B.chord) (B.secondTargetPos t) :=
          congrArg (fun word => vertex B.secondBase word (B.secondTargetPos t)) B.secondWord_eq_append
        _ = _ := vertex_append_left _ _ _ htLt.le
    rw [hvert, inv_mul_cancel]
    exact (D.fam (P.label s)).one_mem

/-- A charged opposite-half target cannot connect to the reversed left connector. -/
theorem secondGapChordSource_not_connected_left
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapChordSources j) {q : ℕ}
    (hq : q < (B.secondGapLeft j).length)
    (hop : IsCompStart (P.label s) (B.secondGapCycle j) q) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
      (B.secondGapCut j (B.secondGapChordTargetIndex j (B.brokenAssignment.first.partner s))) q := by
  classical
  have hlen := B.secondGapLeft_length_le_one j
  have hq0 : q = 0 := by omega
  subst q
  cases hp : HalfGap.previousEntry B.brokenAssignment.index.second j with
  | none =>
    have : B.secondGapLeft j = [] := by simp only [secondGapLeft]; rw [hp]
    simp [this] at hq
  | some e =>
    let t := HalfEntry.entrySource B.brokenAssignment.index.second e
    have ht := (mem_brokenSet_iff.mp (HalfEntry.entrySource_mem B.brokenAssignment.index.second e)).1
    have hstart : B.secondGapStartSide j = B.secondTargetSide t + 1 := by
      simp only [secondGapStartSide]; rw [hp]
    obtain ⟨endPos, hcomp⟩ := hop
    have hcycle := hcomp.1.trans_le hcomp.2.1
    have hletter := hcomp.2.2.1 _ le_rfl hcomp.1 hcycle
    have hown := B.secondGap_leftConnector_isCompOf j e hp 0 hq hcycle
    rw [B.secondGapLocalLabel_leftConnector j e hp 0 hq] at hown
    have hlabel : P.label s = P.label t := eq_of_isCompOf_of_isCompOf hletter hown
    have hleft := listVal_mem_fam_of_isCompOf D (P.label t) (B.secondGapLeft j)
      (B.secondGapLeft_letters j) (B.secondGapLeft_label j e hp)
    have hreverse : RelLetter.listVal (revWord (B.secondGapLeft j)) ∈ D.fam (P.label s) := by
      rw [listVal_revWord, hlabel]
      exact (D.fam (P.label t)).inv_mem hleft
    have hlanding : vertex B.firstBase B.chord (B.secondGapChordFinish j) *
        RelLetter.listVal (revWord (B.secondGapLeft j)) =
        vertex B.secondBase B.secondArc (B.secondTargetPos t + 1) := by
      rw [B.secondGap_arcBase j, hstart, (B.secondArcCut_target ht).2]
    have htComp := B.secondArc_targetComponent ht
    have htLt := htComp.1.trans_le htComp.2.1
    have htLetter := htComp.2.2.1 _ le_rfl htComp.1 htLt
    rw [← hlabel] at htLetter
    apply B.secondGapChordSource_not_connected_of_arc_anchor j s hs htLt
      (Nat.le_succ _) le_rfl htLetter
    rw [vertex_zero, ← hlanding, inv_mul_cancel_left]
    exact hreverse

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapChordSource_not_connected_right
#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapChordSource_not_connected_left
