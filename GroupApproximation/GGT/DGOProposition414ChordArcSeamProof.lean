import GroupApproximation.GGT.DGOProposition414CycleBlocks

/-!
# The last seam of the Proposition 4.14 component families

The remaining case of the charged chord component is the one where the right
connector degenerates while the inherited arc is nonempty, so that the
auxiliary cycle passes straight from the last arc letter into the partner edge
`y_j`.  Dahmani--Guirardel--Osin exclude a same-label arc letter there with

> `y_j` can not be connected to a component of a side of type (2) since
> otherwise `p_{i_j}` is not isolated in `\mathcal P`

(arXiv:1111.7048, proof of Proposition 4.14).  The formal route uses that the
rotated parent word is exactly the wrapped arc followed by the first arc, so
the broken source and the offending arc letter live in one word, in which the
source is isolated; the connector to its chord partner and the closure identity
`firstGap_arcFinish` supply the vertex the two share.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-! ## The rotated parent word is the two inherited arcs -/

/-- Rotating the parent polygon at the second corner lists the wrapped arc and
then the first arc. -/
theorem rotWord_eq_secondArc_append_firstArc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    rotWord P.word B.secondVertex = B.secondArc ++ B.firstArc := by
  have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have hle : B.firstVertex ≤ B.secondVertex := B.split_vertices_ordered
  show P.word.drop B.secondVertex ++ P.word.take B.secondVertex =
    (P.word.drop B.secondVertex ++ P.word.take B.firstVertex) ++
      ((P.word.drop (B.refinedCut (B.firstSide + 1))).take
        (B.refinedCut (B.secondSide + 2) - B.refinedCut (B.firstSide + 1)))
  rw [hleft, hright, List.append_assoc, ← List.take_add,
    show B.firstVertex + (B.secondVertex - B.firstVertex) =
      B.secondVertex from by omega]

/-! ## Isolation of a wrapped target in the rotated parent word -/

/-- A distinguished wrapped source meets no same-label letter of the rotated
parent word whose run reaches a vertex the source is connected to. -/
theorem secondTarget_not_isCompOf_of_connected
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ B.secondTarget)
    (m z : ℕ) (hmlt : m < (rotWord P.word B.secondVertex).length)
    (hzle : z ≤ (rotWord P.word B.secondVertex).length)
    (hmz : m ≤ z) (hzm : z ≤ m + 1)
    (hpos : B.secondTargetPos s < m)
    (hconn : Connected D.fam (P.label s) B.secondBase
      (rotWord P.word B.secondVertex) (B.secondTargetPos s) z) :
    ¬ ((rotWord P.word B.secondVertex)[m]'hmlt).IsCompOf (P.label s) := by
  intro hletter
  have hcompS := B.second_rotated_component hs
  have hisoS := B.second_rotated_isolated hs
  have hletters := letters_rotWord D P.letters B.secondVertex
  obtain ⟨a, bb, ha, hb, hcomp⟩ :=
    exists_isComp_of_isCompOf (P.label s) (rotWord P.word B.secondVertex) m
      hmlt hletter
  have hspan : (vertex B.secondBase (rotWord P.word B.secondVertex) a)⁻¹ *
      vertex B.secondBase (rotWord P.word B.secondVertex) z ∈
      D.fam (P.label s) :=
    span_mem_fam D (P.label s) B.secondBase hletters z hzle a (by omega)
      (fun q hq1 hq2 hq => hcomp.2.2.1 q hq1 (by omega) hq)
  have hconn' : Connected D.fam (P.label s) B.secondBase
      (rotWord P.word B.secondVertex) (B.secondTargetPos s) a := by
    show (vertex B.secondBase (rotWord P.word B.secondVertex)
        (B.secondTargetPos s))⁻¹ *
      vertex B.secondBase (rotWord P.word B.secondVertex) a ∈
        D.fam (P.label s)
    have hc : (vertex B.secondBase (rotWord P.word B.secondVertex)
        (B.secondTargetPos s))⁻¹ *
        vertex B.secondBase (rotWord P.word B.secondVertex) z ∈
        D.fam (P.label s) := hconn
    have hfac : (vertex B.secondBase (rotWord P.word B.secondVertex)
        (B.secondTargetPos s))⁻¹ *
        vertex B.secondBase (rotWord P.word B.secondVertex) a =
        ((vertex B.secondBase (rotWord P.word B.secondVertex)
            (B.secondTargetPos s))⁻¹ *
          vertex B.secondBase (rotWord P.word B.secondVertex) z) *
        ((vertex B.secondBase (rotWord P.word B.secondVertex) a)⁻¹ *
          vertex B.secondBase (rotWord P.word B.secondVertex) z)⁻¹ := by
      group
    rw [hfac]
    exact mul_mem hc (inv_mem hspan)
  have hane : a ≠ B.secondTargetPos s := by
    intro heq
    have hlt : B.secondTargetPos s + 1 <
        (rotWord P.word B.secondVertex).length := by omega
    have hin := hcomp.2.2.1 (B.secondTargetPos s + 1) (by omega) (by omega) hlt
    exact hcompS.2.2.2.2 hlt hin
  exact hisoS.2 a hane ⟨bb, hcomp⟩ hconn'

/-! ## The seam, closed -/

/-- The residual arc seam of the charged chord component holds outright. -/
theorem firstGapChordArcSeam_of_source
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapChordSources j) :
    FirstGapChordArcSeam B j s := by
  classical
  intro hR0 harcPos hoei0 hq hletter
  have hsBroken := (Finset.mem_filter.mp hs).1
  have hsTarget := (mem_brokenSet_iff.mp hsBroken).1
  have howner := (Finset.mem_filter.mp hs).2
  have hedge := B.secondPartnerFirstGapOwner_edge s hsBroken
  rw [howner] at hedge
  have hRightNil : B.firstGapRight j = [] := List.length_eq_zero_iff.mp hR0
  set y := B.brokenAssignment.second.partner s with hy_def
  -- the offending letter is the last letter of the inherited arc
  have hcutEnd : B.firstArcCut (B.firstGapFinishSide j) ≤ B.firstArc.length :=
    B.firstArc_isCutPath.cut.le_length (B.firstGapFinishSide_le j)
  have harcLen : (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)).length =
      B.firstArcCut (B.firstGapFinishSide j) -
        B.firstArcCut (B.firstGapStartSide j) :=
    length_arcWord B.firstArc B.firstArcCut hcutEnd
  have hcycleLen : (B.firstGapCycle j).length =
      (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length +
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)).length := by
    simp only [firstGapCycle, auxiliaryCycleWord, List.length_append,
      OsinComponents.length_revWord]
  have hq' : (B.firstGapLeft j).length +
      ((arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)).length - 1) <
      (B.firstGapCycle j).length := by omega
  have hgetEq : (B.firstGapCycle j)[(B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length - 1]'hq =
      (B.firstGapCycle j)[(B.firstGapLeft j).length +
        ((arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length - 1)]'hq' :=
    getElem_congr_idx (by omega)
  rw [hgetEq] at hletter
  have harcLetter := (isCompOf_auxiliaryCycle_arc_iff (P.label s)
    (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)) (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j)) _ (by omega) hq').mp hletter
  rw [getElem_arcWord B.firstArc B.firstArcCut hcutEnd (by omega)]
    at harcLetter
  -- move it into the rotated parent word
  have hrot := B.rotWord_eq_secondArc_append_firstArc
  have hsecondArcLen := B.secondArc_length_eq
  have hrotLen : (rotWord P.word B.secondVertex).length =
      B.secondArc.length + B.firstArc.length := by
    rw [hrot, List.length_append]
  have hposLt : B.secondTargetPos s < B.secondArc.length := by
    rw [hsecondArcLen]
    exact B.secondTargetPos_lt hsTarget
  have hmlt : B.secondArc.length +
      (B.firstArcCut (B.firstGapFinishSide j) - 1) <
      (rotWord P.word B.secondVertex).length := by omega
  have hletterRot : ((rotWord P.word B.secondVertex)[B.secondArc.length +
      (B.firstArcCut (B.firstGapFinishSide j) - 1)]'hmlt).IsCompOf
      (P.label s) := by
    rw [List.getElem_of_eq hrot hmlt, List.getElem_append_right (by omega),
      getElem_congr_idx (c := B.firstArc)
        (show B.secondArc.length +
            (B.firstArcCut (B.firstGapFinishSide j) - 1) -
              B.secondArc.length =
          B.firstArcCut (B.firstGapStartSide j) +
            ((arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
              (B.firstGapFinishSide j)).length - 1) from by omega)]
    exact harcLetter
  -- the wrapped source is connected to its chord partner
  have hA : (vertex B.secondBase B.secondWord (B.secondTargetPos s))⁻¹ *
      vertex B.firstBase B.chord y ∈ D.fam (P.label s) := by
    have hpc : Connected D.fam (P.label s) B.secondBase B.secondWord
        (B.secondTargetPos s) (B.secondChordPos y) :=
      B.brokenAssignment.second.partner_connected s hsBroken
    have hchordVertex : vertex B.secondBase B.secondWord (B.secondChordPos y) =
        vertex B.firstBase B.chord y := by
      rw [B.secondWord_eq_append,
        show B.secondChordPos y = B.secondArc.length + y from by
          rw [hsecondArcLen]; simp only [secondChordPos],
        vertex_append_add, B.secondArc_endpoint]
    rw [← hchordVertex]
    exact hpc
  -- the partner edge reaches the chord vertex where the arc ends
  have hB : (vertex B.firstBase B.chord y)⁻¹ *
      vertex B.firstBase B.chord (B.firstGapChordStart j) ∈
      D.fam (P.label s) := by
    unfold EdgeBetween at hedge
    by_cases hdir : B.firstGapChordStart j ≤ B.firstGapChordFinish j
    · have hyEq : y = B.firstGapChordStart j := by
        simp only [orientedEdgeIndex, if_pos hdir] at hoei0
        omega
      rw [hyEq, inv_mul_cancel]
      exact one_mem _
    · have hyEq : B.firstGapChordStart j = y + 1 := by
        simp only [orientedEdgeIndex, if_neg hdir] at hoei0
        omega
      rw [hyEq]
      exact span_mem_fam_of_isComp D B.firstBase B.chord_geodesic.1
        (B.secondPartner_chord_isComp s hsBroken)
  -- the two share the vertex at the end of the inherited arc
  have hposvert : vertex B.secondBase (rotWord P.word B.secondVertex)
      (B.secondTargetPos s) =
      vertex B.secondBase B.secondWord (B.secondTargetPos s) := by
    rw [hrot, B.secondWord_eq_append, vertex_append_left _ _ _ (by omega),
      vertex_append_left _ _ _ (by omega)]
  have hzvert : vertex B.secondBase (rotWord P.word B.secondVertex)
      (B.secondArc.length + (B.firstArcCut (B.firstGapFinishSide j) - 1) + 1) =
      vertex B.firstBase B.chord (B.firstGapChordStart j) := by
    have harcFin := B.firstGap_arcFinish j
    rw [hRightNil, RelLetter.listVal_nil, mul_one] at harcFin
    rw [hrot, show B.secondArc.length +
        (B.firstArcCut (B.firstGapFinishSide j) - 1) + 1 =
        B.secondArc.length + B.firstArcCut (B.firstGapFinishSide j) from by
      omega, vertex_append_add, B.secondArc_endpoint]
    exact harcFin
  have hconnRot : Connected D.fam (P.label s) B.secondBase
      (rotWord P.word B.secondVertex) (B.secondTargetPos s)
      (B.secondArc.length + (B.firstArcCut (B.firstGapFinishSide j) - 1) + 1) := by
    show (vertex B.secondBase (rotWord P.word B.secondVertex)
        (B.secondTargetPos s))⁻¹ *
      vertex B.secondBase (rotWord P.word B.secondVertex)
        (B.secondArc.length +
          (B.firstArcCut (B.firstGapFinishSide j) - 1) + 1) ∈
        D.fam (P.label s)
    rw [hposvert, hzvert]
    have hfac : (vertex B.secondBase B.secondWord (B.secondTargetPos s))⁻¹ *
        vertex B.firstBase B.chord (B.firstGapChordStart j) =
        ((vertex B.secondBase B.secondWord (B.secondTargetPos s))⁻¹ *
            vertex B.firstBase B.chord y) *
          ((vertex B.firstBase B.chord y)⁻¹ *
            vertex B.firstBase B.chord (B.firstGapChordStart j)) := by
      group
    rw [hfac]
    exact mul_mem hA hB
  exact B.secondTarget_not_isCompOf_of_connected s hsTarget _ _ hmlt
    (by omega) (by omega) (le_refl _) (by omega) hconnRot hletterRot

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
