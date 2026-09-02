import GroupApproximation.GGT.DGOProposition414ChordArcSeamProof

/-!
# The last seam of the wrapped Proposition 4.14 component family

Wrapped counterpart of `DGOProposition414ChordArcSeamProof`.  The offending
letter is now the last letter of the wrapped inherited arc, and the broken
source is a first-half one, so the ambient word is the same rotation of the
parent polygon, read as the wrapped arc followed by the first arc.  With this
the charged chord component field, and therefore both gap component families,
are unconditional.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-! ## A first-half target is isolated in the rotated parent word -/

/-- The rotation at the second corner keeps a distinguished first-half source
isolated, at the position that the wrapped arc shifts it to. -/
theorem firstTarget_rotated_isolated
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.firstTarget) :
    IsIsolated D.fam (P.label s) B.secondBase (rotWord P.word B.secondVertex)
      (B.secondArc.length + B.firstTargetPos s) := by
  classical
  have hsTarget := (Finset.mem_filter.mp hs).1
  have harc := (Finset.mem_filter.mp hs).2
  have hlow : B.firstVertex ≤ P.cut s := harc.1
  have hhigh : P.cut (s + 1) ≤ B.secondVertex := harc.2
  have hedge := P.target_edge s hsTarget
  have hcomp : IsComp (P.label s) P.word (P.cut s) (P.cut s + 1) := by
    rw [← hedge]
    exact P.target_component s hsTarget
  have hiso := P.target_isolated s hsTarget
  have hJle : B.secondVertex ≤ P.word.length :=
    B.secondVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
  have hbefore : P.cut s + 1 ≤ B.secondVertex := by
    rw [hedge] at hhigh
    exact hhigh
  have hlenEq : B.secondArc.length =
      (P.word.length - B.secondVertex) + B.firstVertex := by
    rw [B.secondArc_length_eq]
    simp only [secondArcLength]
  have hidx : B.secondArc.length + B.firstTargetPos s =
      P.word.length - B.secondVertex + P.cut s := by
    rw [hlenEq]
    simp only [firstTargetPos]
    omega
  rw [hidx]
  by_cases hJend : B.secondVertex = P.word.length
  · have hvertex : vertex P.basepoint P.word B.secondVertex = P.basepoint := by
      rw [hJend, vertex_length_of_closed P.basepoint P.word P.closed]
    have hrot : rotWord P.word B.secondVertex = P.word := by
      simp [hJend, rotWord]
    have hpos : P.word.length - B.secondVertex + P.cut s = P.cut s := by omega
    rw [hpos, hrot]
    show IsIsolated D.fam (P.label s) B.secondBase P.word (P.cut s)
    rw [show B.secondBase = P.basepoint from hvertex]
    exact hiso
  · have hJlt : B.secondVertex < P.word.length := lt_of_le_of_ne hJle hJend
    by_cases hs0 : P.cut s = 0
    · rw [hs0] at hcomp hiso
      have hrot := isIsolated_rotWord_zero_before D (P.label s) P.basepoint
        P.letters P.closed hJlt hcomp (by omega) hiso
      rw [hs0, Nat.add_zero]
      exact hrot
    · exact isIsolated_rotWord_before D (P.label s) P.basepoint
        P.letters P.closed hJlt hcomp (by omega) (by omega) hiso

/-- The isolation of a first-half target in the rotated parent word, in the
shape the wrapped seam consumes. -/
theorem firstTarget_rotated_not_isCompOf_of_connected
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ B.firstTarget)
    (m z : ℕ) (hmlt : m < (rotWord P.word B.secondVertex).length)
    (hzle : z ≤ (rotWord P.word B.secondVertex).length)
    (hmz : m ≤ z) (hzm : z ≤ m + 1)
    (hpos : m < B.secondArc.length + B.firstTargetPos s)
    (hconn : Connected D.fam (P.label s) B.secondBase
      (rotWord P.word B.secondVertex)
      (B.secondArc.length + B.firstTargetPos s) z) :
    ¬ ((rotWord P.word B.secondVertex)[m]'hmlt).IsCompOf (P.label s) := by
  intro hletter
  have hisoS := B.firstTarget_rotated_isolated hs
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
      (rotWord P.word B.secondVertex)
      (B.secondArc.length + B.firstTargetPos s) a := by
    show (vertex B.secondBase (rotWord P.word B.secondVertex)
        (B.secondArc.length + B.firstTargetPos s))⁻¹ *
      vertex B.secondBase (rotWord P.word B.secondVertex) a ∈
        D.fam (P.label s)
    have hc : (vertex B.secondBase (rotWord P.word B.secondVertex)
        (B.secondArc.length + B.firstTargetPos s))⁻¹ *
        vertex B.secondBase (rotWord P.word B.secondVertex) z ∈
        D.fam (P.label s) := hconn
    have hfac : (vertex B.secondBase (rotWord P.word B.secondVertex)
        (B.secondArc.length + B.firstTargetPos s))⁻¹ *
        vertex B.secondBase (rotWord P.word B.secondVertex) a =
        ((vertex B.secondBase (rotWord P.word B.secondVertex)
            (B.secondArc.length + B.firstTargetPos s))⁻¹ *
          vertex B.secondBase (rotWord P.word B.secondVertex) z) *
        ((vertex B.secondBase (rotWord P.word B.secondVertex) a)⁻¹ *
          vertex B.secondBase (rotWord P.word B.secondVertex) z)⁻¹ := by
      group
    rw [hfac]
    exact mul_mem hc (inv_mem hspan)
  have hane : a ≠ B.secondArc.length + B.firstTargetPos s := by omega
  exact hisoS.2 a hane ⟨bb, hcomp⟩ hconn'

/-! ## The wrapped seam, closed -/

/-- Wrapped counterpart of `firstGapChordArcSeam_of_source`. -/
theorem secondGapChordArcSeam_of_source
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapChordSources j) :
    SecondGapChordArcSeam B j s := by
  classical
  intro hR0 harcPos hoei0 hq hletter
  have hsBroken := (Finset.mem_filter.mp hs).1
  have hsTarget := (mem_brokenSet_iff.mp hsBroken).1
  have howner := (Finset.mem_filter.mp hs).2
  have hedge := B.firstPartnerSecondGapOwner_edge s hsBroken
  rw [howner] at hedge
  have hRightNil : B.secondGapRight j = [] := List.length_eq_zero_iff.mp hR0
  set y := B.brokenAssignment.first.partner s with hy_def
  have hcutEnd : B.secondArcCut (B.secondGapFinishSide j) ≤
      B.secondArc.length :=
    B.secondArc_isCutPath.cut.le_length (B.secondGapFinishSide_le j)
  have harcLen : (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)).length =
      B.secondArcCut (B.secondGapFinishSide j) -
        B.secondArcCut (B.secondGapStartSide j) :=
    length_arcWord B.secondArc B.secondArcCut hcutEnd
  have hcycleLen : (B.secondGapCycle j).length =
      (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length +
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)).length := by
    simp only [secondGapCycle, auxiliaryCycleWord, List.length_append,
      OsinComponents.length_revWord]
  have hq' : (B.secondGapLeft j).length +
      ((arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)).length - 1) <
      (B.secondGapCycle j).length := by omega
  have hgetEq : (B.secondGapCycle j)[(B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length - 1]'hq =
      (B.secondGapCycle j)[(B.secondGapLeft j).length +
        ((arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length - 1)]'hq' :=
    getElem_congr_idx (by omega)
  rw [hgetEq] at hletter
  have harcLetter := (isCompOf_auxiliaryCycle_arc_iff (P.label s)
    (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)) (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)) _ (by omega) hq').mp hletter
  rw [getElem_arcWord B.secondArc B.secondArcCut hcutEnd (by omega)]
    at harcLetter
  -- move the letter into the rotated parent word
  have hrot := B.rotWord_eq_secondArc_append_firstArc
  have hrotLen : (rotWord P.word B.secondVertex).length =
      B.secondArc.length + B.firstArc.length := by
    rw [hrot, List.length_append]
  have hmlt : B.secondArcCut (B.secondGapFinishSide j) - 1 <
      (rotWord P.word B.secondVertex).length := by omega
  have hletterRot : ((rotWord P.word B.secondVertex)[
      B.secondArcCut (B.secondGapFinishSide j) - 1]'hmlt).IsCompOf
      (P.label s) := by
    rw [List.getElem_of_eq hrot hmlt, List.getElem_append_left (by omega),
      getElem_congr_idx (c := B.secondArc)
        (show B.secondArcCut (B.secondGapFinishSide j) - 1 =
          B.secondArcCut (B.secondGapStartSide j) +
            ((arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
              (B.secondGapFinishSide j)).length - 1) from by omega)]
    exact harcLetter
  -- the first-half source is connected to its chord partner
  have hposLt : B.firstTargetPos s < B.firstArc.length := by
    rw [B.firstArc_length_eq]
    exact B.firstTargetPos_lt hsTarget
  have hA : (vertex B.firstBase B.firstWord (B.firstTargetPos s))⁻¹ *
      vertex B.firstBase B.chord (y + 1) ∈ D.fam (P.label s) := by
    have hpc : Connected D.fam (P.label s) B.firstBase B.firstWord
        (B.firstTargetPos s) (B.firstChordPos y) :=
      B.brokenAssignment.first.partner_connected s hsBroken
    have hchordVertex : vertex B.firstBase B.firstWord (B.firstChordPos y) =
        vertex B.firstBase B.chord (y + 1) :=
      B.firstBrokenConnectors_partnerStart_vertex s hsBroken
    rw [← hchordVertex]
    exact hpc
  -- the partner edge reaches the chord vertex where the wrapped arc ends
  have hB : (vertex B.firstBase B.chord (y + 1))⁻¹ *
      vertex B.firstBase B.chord (B.secondGapChordStart j) ∈
      D.fam (P.label s) := by
    unfold EdgeBetween at hedge
    by_cases hdir : B.secondGapChordStart j ≤ B.secondGapChordFinish j
    · have hyEq : y = B.secondGapChordStart j := by
        simp only [orientedEdgeIndex, if_pos hdir] at hoei0
        omega
      rw [hyEq]
      have hspan : (vertex B.firstBase B.chord (B.secondGapChordStart j))⁻¹ *
          vertex B.firstBase B.chord (B.secondGapChordStart j + 1) ∈
          D.fam (P.label s) := by
        rw [← hyEq]
        exact span_mem_fam_of_isComp D B.firstBase B.chord_geodesic.1
          (B.firstPartner_chord_isComp s hsBroken)
      have hinv := inv_mem hspan
      have hfac : ((vertex B.firstBase B.chord (B.secondGapChordStart j))⁻¹ *
          vertex B.firstBase B.chord (B.secondGapChordStart j + 1))⁻¹ =
          (vertex B.firstBase B.chord (B.secondGapChordStart j + 1))⁻¹ *
            vertex B.firstBase B.chord (B.secondGapChordStart j) := by
        group
      rw [hfac] at hinv
      exact hinv
    · have hyEq : B.secondGapChordStart j = y + 1 := by
        simp only [orientedEdgeIndex, if_neg hdir] at hoei0
        omega
      rw [hyEq, inv_mul_cancel]
      exact one_mem _
  -- the two share the vertex at the end of the wrapped arc
  have hposvert : vertex B.secondBase (rotWord P.word B.secondVertex)
      (B.secondArc.length + B.firstTargetPos s) =
      vertex B.firstBase B.firstWord (B.firstTargetPos s) := by
    rw [hrot, vertex_append_add, B.secondArc_endpoint, B.firstWord_eq_append,
      vertex_append_left _ _ _ (by omega)]
  have hzvert : vertex B.secondBase (rotWord P.word B.secondVertex)
      (B.secondArcCut (B.secondGapFinishSide j) - 1 + 1) =
      vertex B.firstBase B.chord (B.secondGapChordStart j) := by
    have harcFin := B.secondGap_arcFinish j
    rw [hRightNil, RelLetter.listVal_nil, mul_one] at harcFin
    rw [hrot, vertex_append_left _ _ _ (by omega),
      show B.secondArcCut (B.secondGapFinishSide j) - 1 + 1 =
        B.secondArcCut (B.secondGapFinishSide j) from by omega]
    exact harcFin
  have hconnRot : Connected D.fam (P.label s) B.secondBase
      (rotWord P.word B.secondVertex)
      (B.secondArc.length + B.firstTargetPos s)
      (B.secondArcCut (B.secondGapFinishSide j) - 1 + 1) := by
    show (vertex B.secondBase (rotWord P.word B.secondVertex)
        (B.secondArc.length + B.firstTargetPos s))⁻¹ *
      vertex B.secondBase (rotWord P.word B.secondVertex)
        (B.secondArcCut (B.secondGapFinishSide j) - 1 + 1) ∈
        D.fam (P.label s)
    rw [hposvert, hzvert]
    have hfac : (vertex B.firstBase B.firstWord (B.firstTargetPos s))⁻¹ *
        vertex B.firstBase B.chord (B.secondGapChordStart j) =
        ((vertex B.firstBase B.firstWord (B.firstTargetPos s))⁻¹ *
            vertex B.firstBase B.chord (y + 1)) *
          ((vertex B.firstBase B.chord (y + 1))⁻¹ *
            vertex B.firstBase B.chord (B.secondGapChordStart j)) := by
      group
    rw [hfac]
    exact mul_mem hA hB
  exact B.firstTarget_rotated_not_isCompOf_of_connected s hsTarget _ _ hmlt
    (by omega) (by omega) (le_refl _) (by omega) hconnRot hletterRot

/-! ## Both component families, unconditionally -/

/-- The charged chord component field of `FirstGapComponentFamily`, with no
residual hypothesis. -/
theorem firstGapChordComponentFieldFull
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapChordSources j) :
    IsComp (B.firstGapLocalLabel j
        (B.firstGapChordTargetIndex j
          (B.brokenAssignment.second.partner s)))
      (B.firstGapCycle j)
      (B.firstGapCut j (B.firstGapChordTargetIndex j
        (B.brokenAssignment.second.partner s)))
      (B.firstGapCut j (B.firstGapChordTargetIndex j
        (B.brokenAssignment.second.partner s) + 1)) :=
  B.firstGapChordComponentField j s hs (B.firstGapChordArcSeam_of_source j s hs)

/-- The charged chord component field of `SecondGapComponentFamily`, with no
residual hypothesis. -/
theorem secondGapChordComponentFieldFull
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapChordSources j) :
    IsComp (B.secondGapLocalLabel j
        (B.secondGapChordTargetIndex j
          (B.brokenAssignment.first.partner s)))
      (B.secondGapCycle j)
      (B.secondGapCut j (B.secondGapChordTargetIndex j
        (B.brokenAssignment.first.partner s)))
      (B.secondGapCut j (B.secondGapChordTargetIndex j
        (B.brokenAssignment.first.partner s) + 1)) :=
  B.secondGapChordComponentField j s hs
    (B.secondGapChordArcSeam_of_source j s hs)

/-- Both Proposition 4.14 gap component families, with no residual
hypothesis. -/
theorem exists_gapComponentFamilies
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    Nonempty (FirstGapComponentFamily B) ∧
      Nonempty (SecondGapComponentFamily B) :=
  B.exists_gapComponentFamilies_of_chordArcSeams
    (fun j s hs => B.firstGapChordArcSeam_of_source j s hs)
    (fun j s hs => B.secondGapChordArcSeam_of_source j s hs)

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
