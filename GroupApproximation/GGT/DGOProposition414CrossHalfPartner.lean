import GroupApproximation.GGT.DGOProposition414PartnerEndpoints

/-!
# Cross-half separation of chord partners

A chord component charged to a broken source in one balanced half is used as
the type-(4) target in the opposite half.  The key compatibility fact is that
the same chord edge cannot also be selected by an opposite-half broken source
of the same peripheral label: otherwise the two original distinguished
components are connected through that edge, contradicting their isolation in
the original polygon.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- A first-half source vertex is the corresponding distinguished vertex of
the original polygon. -/
theorem firstSource_vertex_original
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ B.componentPlacement.firstTarget) :
    vertex B.firstBase B.firstWord (B.componentPlacement.firstPos s) =
      vertex P.basepoint P.word (P.cut s) := by
  classical
  have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have hEnd : B.refinedCut (B.secondSide + 2) ≤ P.word.length := by
    rw [hright]
    exact B.secondVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
  have hlt := B.firstTargetPos_lt hs
  have hpos : B.componentPlacement.firstPos s = B.firstTargetPos s := rfl
  have hcut : B.firstVertex + B.firstTargetPos s = P.cut s := by
    have hs' := Finset.mem_filter.mp hs
    unfold targetInFirstArc at hs'
    simp only [firstTargetPos]
    omega
  rw [hpos, firstBase, ← hleft, firstWord,
    vertex_firstHalf P.word P.basepoint B.refinedCut
      (show B.firstTargetPos s ≤
        B.refinedCut (B.secondSide + 2) -
          B.refinedCut (B.firstSide + 1) by
        simpa only [hleft, hright, firstArcLength] using hlt.le)
      hEnd B.chord,
    hleft, hcut]

/-- A wrapped-half source vertex is the corresponding distinguished vertex of
the original closed polygon, including the branch across the old word seam. -/
theorem secondSource_vertex_original
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ B.componentPlacement.secondTarget) :
    vertex B.secondBase B.secondWord (B.componentPlacement.secondPos s) =
      vertex P.basepoint P.word (P.cut s) := by
  classical
  have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have hEnd : B.refinedCut (B.secondSide + 2) ≤ P.word.length := by
    rw [hright]
    exact B.secondVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
  have hStartEnd : B.refinedCut (B.firstSide + 1) ≤
      B.refinedCut (B.secondSide + 2) := by
    rw [hleft, hright]
    exact B.split_vertices_ordered
  have hlt := B.secondTargetPos_lt hs
  have hpos : B.componentPlacement.secondPos s = B.secondTargetPos s := rfl
  rw [hpos, secondBase, ← hright, secondWord,
    vertex_secondHalf_rotWord P.word P.basepoint B.refinedCut hStartEnd hEnd
      (show B.secondTargetPos s ≤
        (P.word.length - B.refinedCut (B.secondSide + 2)) +
          B.refinedCut (B.firstSide + 1) by
        simpa only [hleft, hright, secondArcLength] using hlt.le)
      B.chord,
    hright]
  have hsecondLe : B.secondVertex ≤ P.word.length := by
    rwa [hright] at hEnd
  by_cases hafter : B.secondVertex ≤ P.cut s
  · rw [secondTargetPos, if_pos hafter,
      vertex_rotWord_le P.basepoint P.word hsecondLe
        (P.cut s - B.secondVertex)
        (by
          have hsP : s ∈ P.target := (Finset.mem_filter.mp hs).1
          have hcutLen := (P.target_component s hsP).1.trans_le
            (P.target_component s hsP).2.1
          omega)]
    congr 2
    omega
  · have hcutLe : P.cut s ≤ B.secondVertex := by omega
    rw [secondTargetPos, if_neg hafter]
    exact vertex_rotWord_add P.basepoint P.word hsecondLe P.closed
      (P.word.length - B.secondVertex + P.cut s) (P.cut s) rfl hcutLe

/-- Opposite-half broken sources of the same label select distinct chord
edges.  This is the exact cross-half allocation invariant for the type-(4)
factor `y_j`. -/
theorem crossHalf_partner_ne_of_label_eq
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s t : ℕ)
    (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives)
    (ht : t ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives)
    (hlabel : P.label s = P.label t) :
    B.brokenAssignment.first.partner s ≠
      B.brokenAssignment.second.partner t := by
  classical
  intro hpartner
  have hsTarget := (mem_brokenSet_iff.mp hs).1
  have htTarget := (mem_brokenSet_iff.mp ht).1
  have hsP : s ∈ P.target := by
    exact (Finset.mem_filter.mp hsTarget).1
  have htP : t ∈ P.target := by
    exact (Finset.mem_filter.mp htTarget).1
  have hst : s ≠ t := by
    intro hst
    subst t
    exact (Finset.disjoint_left.mp B.target_partition.1) hsTarget htTarget
  have hcut : P.cut s ≠ P.cut t := by
    intro h
    exact hst (target_cut_injective P hsP htP h)
  let y := B.brokenAssignment.first.partner s
  have hy : y < B.chord.length :=
    B.brokenAssignment.first.partner_lt s hs
  have hfirst := B.brokenAssignment.first.partner_connected s hs
  have hsecond := B.brokenAssignment.second.partner_connected t ht
  have hfirstVertex := B.firstBrokenConnectors_partnerStart_vertex s hs
  have hsecondVertex := B.secondBrokenConnectors_partnerStart_vertex t ht
  have hsourceFirst := B.firstSource_vertex_original s hsTarget
  have hsourceSecond := B.secondSource_vertex_original t htTarget
  have hf :
      (vertex P.basepoint P.word (P.cut s))⁻¹ *
          vertex B.firstBase B.chord (y + 1) ∈ D.fam (P.label s) := by
    change (vertex B.firstBase B.firstWord
      (B.componentPlacement.firstPos s))⁻¹ *
        vertex B.firstBase B.firstWord
          (B.firstChordPos (B.brokenAssignment.first.partner s)) ∈
            D.fam (P.label s) at hfirst
    rw [hsourceFirst, hfirstVertex] at hfirst
    exact hfirst
  have he :
      (vertex P.basepoint P.word (P.cut t))⁻¹ *
          vertex B.firstBase B.chord y ∈ D.fam (P.label s) := by
    change (vertex B.secondBase B.secondWord
      (B.componentPlacement.secondPos t))⁻¹ *
        vertex B.secondBase B.secondWord
          (B.secondChordPos (B.brokenAssignment.second.partner t)) ∈
            D.fam (P.label t) at hsecond
    rw [hsourceSecond, hsecondVertex, ← hpartner] at hsecond
    simpa only [hlabel, y] using hsecond
  have hySpan :
      (vertex B.firstBase B.chord y)⁻¹ *
          vertex B.firstBase B.chord (y + 1) ∈ D.fam (P.label s) := by
    -- The selected first-half letter is the reverse of global chord edge `y`.
    have hrevSpan :
        (vertex B.firstBase B.chord (y + 1))⁻¹ *
          vertex B.firstBase B.chord y ∈ D.fam (P.label s) := by
      -- The component span itself gives the required reversed chord edge.
      have hspan := (B.firstBrokenConnectors s hs).partnerComponent
      have hmem := span_mem_fam_of_isComp D B.firstBase B.firstWord_letters hspan
      rw [B.firstBrokenConnectors_partnerStart_vertex s hs,
        B.firstBrokenConnectors_partnerEnd_vertex s hs] at hmem
      exact hmem
    simpa only [mul_inv_rev, inv_inv] using inv_mem hrevSpan
  have hconn : Connected D.fam (P.label s) P.basepoint P.word
      (P.cut s) (P.cut t) := by
    show (vertex P.basepoint P.word (P.cut s))⁻¹ *
      vertex P.basepoint P.word (P.cut t) ∈ D.fam (P.label s)
    have hmul := mul_mem hf (mul_mem (inv_mem hySpan) (inv_mem he))
    have heq :
        ((vertex P.basepoint P.word (P.cut s))⁻¹ *
            vertex B.firstBase B.chord (y + 1)) *
          (((vertex B.firstBase B.chord y)⁻¹ *
              vertex B.firstBase B.chord (y + 1))⁻¹ *
            ((vertex P.basepoint P.word (P.cut t))⁻¹ *
              vertex B.firstBase B.chord y)⁻¹) =
          (vertex P.basepoint P.word (P.cut s))⁻¹ *
            vertex P.basepoint P.word (P.cut t) := by
      group
    rw [heq] at hmul
    exact hmul
  have htStart : IsCompStart (P.label s) P.word (P.cut t) := by
    refine ⟨P.cut (t + 1), ?_⟩
    simpa only [hlabel] using P.target_component t htP
  exact P.target_isolated s hsP |>.2 (P.cut t) hcut.symm htStart hconn

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
