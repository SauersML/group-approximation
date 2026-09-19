import GroupApproximation.GGT.DGOProposition414FirstArcSeparation

/-!
# Separating inherited first-half targets from the two connectors

The right connector starts at the following broken source. The reversed left
connector ends at the preceding broken source's terminal vertex. A connection
from an inherited survivor to either connector would therefore connect it to
that broken source in the half word, contradicting its isolation there.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

omit [Group G] in
private theorem component_label_unique {a : RelLetter G Lambda} {lam mu : Lambda}
    (h1 : a.IsCompOf lam) (h2 : a.IsCompOf mu) : lam = mu := by
  cases a with
  | base _ => exact False.elim h1
  | comp nu _ => exact (show nu = lam from h1).symm.trans h2

/-- An inherited survivor cannot connect to the right connector of its gap. -/
theorem firstGapArcSource_not_connected_right
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j) {r : ℕ}
    (hr : r < (B.firstGapRight j).length)
    (hop : IsCompStart (P.label s) (B.firstGapCycle j)
      ((B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length + r)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
      (B.firstGapCut j ((B.firstGapLeft j).length + (B.firstTargetSide s - B.firstGapStartSide j)))
      ((B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length + r) := by
  intro hconn
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
    have hsData := Finset.mem_filter.mp hs
    have hfinish : B.firstGapFinishSide j = B.firstTargetSide t := by
      simp only [firstGapFinishSide]; rw [hn]
    have hpos : B.firstTargetPos s < B.firstTargetPos t :=
      B.firstTargetPos_lt_of_side_lt hsData.1 ht (by rw [hfinish] at hsData; exact hsData.2.2)
    obtain ⟨endPos, hcomp⟩ := hop
    have hcycle := hcomp.1.trans_le hcomp.2.1
    have hletter := hcomp.2.2.1 _ le_rfl hcomp.1 hcycle
    have hown := B.firstGap_rightConnector_isCompOf j e hn 0 hr hcycle
    rw [B.firstGapLocalLabel_rightConnector j e hn 0 hr] at hown
    have hlabel : P.label s = P.label t := component_label_unique hletter hown
    have hsurv := B.firstGapArcSource_survives j s hs
    have hconnWord : Connected D.fam (P.label s) B.firstBase B.firstWord
        (B.firstTargetPos s) (B.firstTargetPos t) := by
      change _ ∈ D.fam (P.label s) at hconn ⊢
      rw [B.firstGapArcSource_vertex j s hs, Nat.add_zero,
        B.firstSeparation_arcBlock_length j, B.firstSeparation_vertex_arc j le_rfl,
        Nat.add_sub_of_le (B.firstSeparation_arcCut_mono j), hfinish,
        (B.firstArcCut_target ht).1] at hconn
      exact hconn
    have htStart := B.componentPlacement.first_start t ht
    change IsCompStart (P.label t) B.firstWord (B.firstTargetPos t) at htStart
    rw [← hlabel] at htStart
    exact hsurv.2.2 (B.firstTargetPos t) (by change _ ≠ B.firstTargetPos s; omega) htStart hconnWord

/-- An inherited survivor cannot connect to the reversed left connector. -/
theorem firstGapArcSource_not_connected_left
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j) {q : ℕ}
    (hq : q < (B.firstGapLeft j).length)
    (hop : IsCompStart (P.label s) (B.firstGapCycle j) q) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
      (B.firstGapCut j ((B.firstGapLeft j).length + (B.firstTargetSide s - B.firstGapStartSide j))) q := by
  intro hconn
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
    have hsData := Finset.mem_filter.mp hs
    have hstart : B.firstGapStartSide j = B.firstTargetSide t + 1 := by
      simp only [firstGapStartSide]; rw [hp]
    have hpos : B.firstTargetPos t < B.firstTargetPos s :=
      B.firstTargetPos_lt_of_side_lt ht hsData.1 (by rw [hstart] at hsData; omega)
    obtain ⟨endPos, hcomp⟩ := hop
    have hcycle := hcomp.1.trans_le hcomp.2.1
    have hletter := hcomp.2.2.1 _ le_rfl hcomp.1 hcycle
    have hown := B.firstGap_leftConnector_isCompOf j e hp 0 hq hcycle
    rw [B.firstGapLocalLabel_leftConnector j e hp 0 hq] at hown
    have hlabel : P.label s = P.label t := component_label_unique hletter hown
    have hleft := listVal_mem_fam_of_isCompOf D (P.label t) (B.firstGapLeft j)
      (B.firstGapLeft_letters j) (B.firstGapLeft_label j e hp)
    have hreverse : RelLetter.listVal (revWord (B.firstGapLeft j)) ∈ D.fam (P.label s) := by
      rw [listVal_revWord, hlabel]
      exact (D.fam (P.label t)).inv_mem hleft
    have hlanding : vertex B.firstBase B.chord (B.firstGapChordFinish j) *
        RelLetter.listVal (revWord (B.firstGapLeft j)) =
        vertex B.firstBase B.firstWord (B.firstTargetPos t + 1) := by
      rw [B.firstGap_arcBase j, hstart, (B.firstArcCut_target ht).2]
      symm
      calc
        vertex B.firstBase B.firstWord (B.firstTargetPos t + 1) =
            vertex B.firstBase (B.firstArc ++ revWord B.chord) (B.firstTargetPos t + 1) :=
          congrArg (fun word => vertex B.firstBase word (B.firstTargetPos t + 1)) B.firstWord_eq_append
        _ = _ := vertex_append_left _ _ _
          (by rw [B.firstArc_length_eq]; exact Nat.succ_le_of_lt (B.firstTargetPos_lt ht))
    have hspan := B.firstSourceSpan_mem t ht
    change (vertex B.firstBase B.firstWord (B.firstTargetPos t))⁻¹ *
      vertex B.firstBase B.firstWord (B.firstTargetPos t + 1) ∈ D.fam (P.label t) at hspan
    rw [← hlabel] at hspan
    change _ ∈ D.fam (P.label s) at hconn
    rw [B.firstGapArcSource_vertex j s hs, vertex_zero] at hconn
    have hconnWord : Connected D.fam (P.label s) B.firstBase B.firstWord
        (B.firstTargetPos s) (B.firstTargetPos t) := by
      have hm := (D.fam (P.label s)).mul_mem ((D.fam (P.label s)).mul_mem hconn hreverse)
        ((D.fam (P.label s)).inv_mem hspan)
      change _ ∈ D.fam (P.label s)
      convert hm using 1
      rw [← hlanding]
      group
    have hsurv := B.firstGapArcSource_survives j s hs
    have htStart := B.componentPlacement.first_start t ht
    change IsCompStart (P.label t) B.firstWord (B.firstTargetPos t) at htStart
    rw [← hlabel] at htStart
    exact hsurv.2.2 (B.firstTargetPos t) (by change _ ≠ B.firstTargetPos s; omega) htStart hconnWord

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapArcSource_not_connected_right
#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapArcSource_not_connected_left
