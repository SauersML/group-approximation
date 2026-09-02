import GroupApproximation.GGT.DGOProposition414ComponentFamiliesAux

/-!
# The terminal seam of an inherited arc in a Proposition 4.14 gap child

Dahmani--Guirardel--Osin build, for each gap between two consecutive broken
sources, the auxiliary cycle

`c_j = e_{j-1}^{-1} p_{i_{j-1}+1} … p_{i_j-1} f_j [(y_j)_-,(y_{j-1})_+]`,

whose four blocks are the reversed left connector, the inherited arc, the
right connector, and an oriented segment of the geodesic chord.  For a target
retained inside the gap, the letter *after* its edge in `c_j` lies in exactly
one of three places, and this file discharges the first two of them:

* the letter is still an arc letter, and the parent component's own maximality
  clause excludes it;
* the letter is the right connector, whose label is the label of the *next*
  broken source `p_{i_j}`.  Because the gap arc ends where that source begins,
  the two edges are consecutive single-edge components of the parent arc, so
  their labels differ --- otherwise the parent component would not be maximal.

The remaining place is the first letter of the oriented chord segment, reached
only when the right connector degenerates to the empty path.  DGO exclude it
with

> a path `p_i ∈ I₁ \ J₁` can not be connected to a component of `t` according
> to our choice of `p_{i_1}, …, p_{i_l}`

(arXiv:1111.7048, proof of Proposition 4.14).  That clause is named here as
`FirstGapArcChordSeam`, strictly smaller than the exclusion it feeds: it
speaks about one letter at one seam, under two extra premises.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Letters of the chord block of an auxiliary cycle -/

/-- The chord letters of an auxiliary cycle keep their labels at the shifted
positions.  This is the type-(4)/(5) analogue of
`isCompOf_auxiliaryCycle_arc_iff`. -/
theorem isCompOf_auxiliaryCycle_chord_iff
    (lam : Λ) (left arc right chord : List (RelLetter G Λ))
    (r : ℕ) (hr : r < chord.length)
    (hrCycle : left.length + arc.length + right.length + r <
      (auxiliaryCycleWord left arc right chord).length) :
    ((auxiliaryCycleWord left arc right chord)[
        left.length + arc.length + right.length + r]'hrCycle).IsCompOf lam ↔
      (chord[r]'hr).IsCompOf lam := by
  have hrevLength : (revWord left).length = left.length :=
    OsinComponents.length_revWord left
  have hprefix : ((revWord left ++ arc) ++ right).length ≤
      left.length + arc.length + right.length + r := by
    simp only [List.length_append, hrevLength]
    omega
  have hidx : left.length + arc.length + right.length + r -
      ((revWord left ++ arc) ++ right).length = r := by
    simp only [List.length_append, hrevLength]
    omega
  unfold auxiliaryCycleWord
  rw [List.getElem_append_right hprefix]
  exact iff_of_eq
    (congrArg (RelLetter.IsCompOf lam) (getElem_congr_idx (c := chord) hidx))

/-- A child chord read backwards from the far endpoint of the parent chord
opens with the same letter as the reversed parent chord. -/
theorem isCompOf_head_orientedSegment_fromEnd
    (lam : Λ) (word : List (RelLetter G Λ)) {cs cf : ℕ}
    (hcs : cs = word.length) (hcf : cf < word.length)
    (hseg : 0 < (orientedSegment word cs cf).length)
    (hrev : 0 < (revWord word).length) :
    ((orientedSegment word cs cf)[0]'hseg).IsCompOf lam ↔
      ((revWord word)[0]'hrev).IsCompOf lam := by
  subst hcs
  have hdrop : (word.drop cf).length = word.length - cf := List.length_drop
  have heq : orientedSegment word word.length cf = revWord (word.drop cf) := by
    rw [orientedSegment, if_neg (by omega)]
    congr 1
    exact List.take_of_length_le (by omega)
  have hlast : word.length - 1 < word.length := by omega
  have hleft : ((orientedSegment word word.length cf)[0]'hseg).IsCompOf lam ↔
      ((word.drop cf)[(word.drop cf).length - 1]'(by omega)).IsCompOf lam := by
    rw [List.getElem_of_eq heq hseg]
    exact isCompOf_getElem_revWord' (word.drop cf) lam _ _ rfl
  have hright : ((revWord word)[0]'hrev).IsCompOf lam ↔
      (word[word.length - 1]'hlast).IsCompOf lam :=
    isCompOf_getElem_revWord' word lam _ _ rfl
  have hmid : (word.drop cf)[(word.drop cf).length - 1]'(by omega) =
      word[word.length - 1]'hlast := by
    rw [List.getElem_drop]
    exact getElem_congr_idx (by omega)
  rw [hleft, hright, hmid]

/-- A child chord read forwards from the near endpoint of the parent chord
opens with the same letter as the parent chord. -/
theorem isCompOf_head_orientedSegment_fromStart
    (lam : Λ) (word : List (RelLetter G Λ)) {cs cf : ℕ}
    (hcs : cs = 0)
    (hseg : 0 < (orientedSegment word cs cf).length)
    (hhead : 0 < word.length) :
    ((orientedSegment word cs cf)[0]'hseg).IsCompOf lam ↔
      (word[0]'hhead).IsCompOf lam := by
  subst hcs
  have heq : orientedSegment word 0 cf = word.take cf := by
    rw [orientedSegment, if_pos (Nat.zero_le cf)]
    simp
  rw [List.getElem_of_eq heq hseg]
  simp

/-! ## Heads of a child chord anchored at a component of the parent chord -/

/-- If `[y, y+1)` is a component of `word` and a child segment starts at
`y + 1` and runs forwards, its first letter is `word[y+1]`, excluded by the
component's own maximality clause. -/
theorem not_isCompOf_head_orientedSegment_succ
    (lam : Λ) (word : List (RelLetter G Λ)) {y cf : ℕ}
    (hcomp : IsComp lam word y (y + 1)) (hle : y + 1 ≤ cf)
    (hseg : 0 < (orientedSegment word (y + 1) cf).length) :
    ¬ ((orientedSegment word (y + 1) cf)[0]'hseg).IsCompOf lam := by
  have heq : orientedSegment word (y + 1) cf =
      (word.drop (y + 1)).take (cf - (y + 1)) := by
    rw [orientedSegment, if_pos hle]
  have hpos : 0 < ((word.drop (y + 1)).take (cf - (y + 1))).length := by
    rw [← heq]
    exact hseg
  have hlen : ((word.drop (y + 1)).take (cf - (y + 1))).length =
      min (cf - (y + 1)) (word.length - (y + 1)) := by
    rw [List.length_take, List.length_drop]
  have hlt : y + 1 < word.length := by
    rw [hlen] at hpos
    omega
  intro hletter
  rw [List.getElem_of_eq heq hseg, List.getElem_take,
    List.getElem_drop] at hletter
  exact hcomp.2.2.2.2 hlt hletter

/-- If `[y, y+1)` is a component of `word` and a child segment starts at `y`
and runs backwards, its first letter is the inverse of `word[y-1]`, excluded
by the component's predecessor clause. -/
theorem not_isCompOf_head_orientedSegment_pred
    (lam : Λ) (word : List (RelLetter G Λ)) {y cf : ℕ}
    (hcomp : IsComp lam word y (y + 1)) (hle : cf ≤ y)
    (hseg : 0 < (orientedSegment word y cf).length) :
    ¬ ((orientedSegment word y cf)[0]'hseg).IsCompOf lam := by
  have hylen : y + 1 ≤ word.length := hcomp.2.1
  have hne : ¬ (y ≤ cf) := by
    intro hyc
    have hyeq : y = cf := le_antisymm hyc hle
    rw [orientedSegment, if_pos hyc, hyeq] at hseg
    simp at hseg
  have heq : orientedSegment word y cf =
      revWord ((word.drop cf).take (y - cf)) := by
    rw [orientedSegment, if_neg hne]
  have hLlen : ((word.drop cf).take (y - cf)).length = y - cf := by
    rw [List.length_take, List.length_drop]
    omega
  have ht : ((word.drop cf).take (y - cf)).length - 1 <
      ((word.drop cf).take (y - cf)).length := by
    rw [hLlen]
    omega
  have hrev : 0 < (revWord ((word.drop cf).take (y - cf))).length := by
    rw [OsinComponents.length_revWord, hLlen]
    omega
  have hiff := isCompOf_getElem_revWord' ((word.drop cf).take (y - cf)) lam
    (m := 0) hrev ht rfl
  have hidx : cf + (((word.drop cf).take (y - cf)).length - 1) = y - 1 := by
    rw [hLlen]
    omega
  have hy1 : y - 1 < word.length := by omega
  intro hletter
  rw [List.getElem_of_eq heq hseg, hiff, List.getElem_take,
    List.getElem_drop] at hletter
  have hfinal : (word[y - 1]'hy1).IsCompOf lam := by
    rw [← getElem_congr_idx (c := word) hidx]
    exact hletter
  exact hcomp.2.2.2.1 (y - 1) (by omega) hy1 hfinal

namespace BalancedSplitData

/-! ## The residual chord seam -/

/-- The chord-seam exclusion for an inherited first-gap source: when the gap
arc ends at the retained source and the right connector is the empty path, the
first letter of the oriented child chord does not carry the source's label.
This is DGO's "`p_i ∈ I₁ \ J₁` can not be connected to a component of `t`",
localized to one letter. -/
def FirstGapArcChordSeam
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) : Prop :=
  (B.firstGapRight j).length = 0 →
    B.firstArcCut (B.firstTargetSide s) -
        B.firstArcCut (B.firstGapStartSide j) + 1 =
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)).length →
    ∀ hn : (B.firstGapLeft j).length +
        (B.firstArcCut (B.firstTargetSide s) -
          B.firstArcCut (B.firstGapStartSide j)) + 1 <
        (B.firstGapCycle j).length,
      ¬ ((B.firstGapCycle j)[
          (B.firstGapLeft j).length +
            (B.firstArcCut (B.firstTargetSide s) -
              B.firstArcCut (B.firstGapStartSide j)) + 1]'hn).IsCompOf
        (P.label s)

/-- The wrapped chord-seam exclusion. -/
def SecondGapArcChordSeam
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) : Prop :=
  (B.secondGapRight j).length = 0 →
    B.secondArcCut (B.secondTargetSide s) -
        B.secondArcCut (B.secondGapStartSide j) + 1 =
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)).length →
    ∀ hn : (B.secondGapLeft j).length +
        (B.secondArcCut (B.secondTargetSide s) -
          B.secondArcCut (B.secondGapStartSide j)) + 1 <
        (B.secondGapCycle j).length,
      ¬ ((B.secondGapCycle j)[
          (B.secondGapLeft j).length +
            (B.secondArcCut (B.secondTargetSide s) -
              B.secondArcCut (B.secondGapStartSide j)) + 1]'hn).IsCompOf
        (P.label s)

/-! ### Models -/

/-- A nonempty right connector makes the first-gap chord seam vacuous. -/
theorem firstGapArcChordSeam_of_rightConnector
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hright : 0 < (B.firstGapRight j).length) :
    FirstGapArcChordSeam B j s := by
  intro hzero
  exact absurd hzero (by omega)

/-- A nonempty right connector makes the wrapped chord seam vacuous. -/
theorem secondGapArcChordSeam_of_rightConnector
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hright : 0 < (B.secondGapRight j).length) :
    SecondGapArcChordSeam B j s := by
  intro hzero
  exact absurd hzero (by omega)

/-- The degenerate empty-cycle model satisfies the first-gap chord seam. -/
theorem firstGapArcChordSeam_of_emptyCycle
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hcycle : B.firstGapCycle j = []) :
    FirstGapArcChordSeam B j s := by
  intro _ _ hn
  exact absurd hn (by rw [hcycle]; simp)

/-- The degenerate empty-cycle model satisfies the wrapped chord seam. -/
theorem secondGapArcChordSeam_of_emptyCycle
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hcycle : B.secondGapCycle j = []) :
    SecondGapArcChordSeam B j s := by
  intro _ _ hn
  exact absurd hn (by rw [hcycle]; simp)

/-! ## The connector seam: consecutive parent components have distinct labels -/

/-- If the inherited arc of a first-half gap ends exactly at the next broken
source, the retained source and that broken source are consecutive one-edge
components of the parent arc, so their peripheral labels differ.  This is the
maximality clause of the parent component, in the form DGO uses when the
connector `f_j` is read immediately after `p_{i_j-1}`. -/
theorem firstGapArcSource_label_ne_nextEntry
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.first j = some e)
    (hterminal :
      B.firstArcCut (B.firstTargetSide s) -
          B.firstArcCut (B.firstGapStartSide j) + 1 =
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length) :
    P.label s ≠
      P.label (HalfEntry.entrySource B.brokenAssignment.index.first e) := by
  have hsData := Finset.mem_filter.mp hs
  have htBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
  have htTarget := (mem_brokenSet_iff.mp htBroken).1
  have hcutEnd : B.firstArcCut (B.firstGapFinishSide j) ≤ B.firstArc.length :=
    B.firstArc_isCutPath.cut.le_length (B.firstGapFinishSide_le j)
  have harcLen : (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)).length =
      B.firstArcCut (B.firstGapFinishSide j) -
        B.firstArcCut (B.firstGapStartSide j) :=
    length_arcWord B.firstArc B.firstArcCut hcutEnd
  have hfinish : B.firstGapFinishSide j =
      B.firstTargetSide (HalfEntry.entrySource
        B.brokenAssignment.index.first e) := by
    simp only [firstGapFinishSide]
    rw [he]
  have hposT : B.firstArcCut (B.firstGapFinishSide j) =
      B.firstTargetPos (HalfEntry.entrySource
        B.brokenAssignment.index.first e) := by
    rw [hfinish, (B.firstArcCut_target htTarget).1]
  have hposS : B.firstArcCut (B.firstTargetSide s) = B.firstTargetPos s :=
    (B.firstArcCut_target hsData.1).1
  have hstartLe : B.firstArcCut (B.firstGapStartSide j) ≤
      B.firstArcCut (B.firstTargetSide s) :=
    B.firstArc_isCutPath.cut.mono_le hsData.2.1
  have hadj : B.firstTargetPos s + 1 =
      B.firstTargetPos (HalfEntry.entrySource
        B.brokenAssignment.index.first e) := by
    rw [← hposS, ← hposT]
    omega
  have hltT : B.firstTargetPos (HalfEntry.entrySource
      B.brokenAssignment.index.first e) < B.firstArc.length := by
    have hend := (B.firstArc_targetComponent htTarget).2.1
    omega
  have hltS : B.firstTargetPos s + 1 < B.firstArc.length := by omega
  intro hEqLabel
  have hletterT := (B.firstArc_targetComponent htTarget).2.2.1
    (B.firstTargetPos (HalfEntry.entrySource
      B.brokenAssignment.index.first e)) le_rfl (by omega) hltT
  have hgoal : (B.firstArc[B.firstTargetPos s + 1]'hltS).IsCompOf
      (P.label s) := by
    rw [getElem_congr_idx hadj, hEqLabel]
    exact hletterT
  exact (B.firstArc_targetComponent hsData.1).2.2.2.2 hltS hgoal

/-- Wrapped counterpart of `firstGapArcSource_label_ne_nextEntry`. -/
theorem secondGapArcSource_label_ne_nextEntry
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (he : HalfGap.nextEntry B.brokenAssignment.index.second j = some e)
    (hterminal :
      B.secondArcCut (B.secondTargetSide s) -
          B.secondArcCut (B.secondGapStartSide j) + 1 =
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length) :
    P.label s ≠
      P.label (HalfEntry.entrySource B.brokenAssignment.index.second e) := by
  have hsData := Finset.mem_filter.mp hs
  have htBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.second e
  have htTarget := (mem_brokenSet_iff.mp htBroken).1
  have hcutEnd : B.secondArcCut (B.secondGapFinishSide j) ≤
      B.secondArc.length :=
    B.secondArc_isCutPath.cut.le_length (B.secondGapFinishSide_le j)
  have harcLen : (arcWord B.secondArc B.secondArcCut
      (B.secondGapStartSide j) (B.secondGapFinishSide j)).length =
      B.secondArcCut (B.secondGapFinishSide j) -
        B.secondArcCut (B.secondGapStartSide j) :=
    length_arcWord B.secondArc B.secondArcCut hcutEnd
  have hfinish : B.secondGapFinishSide j =
      B.secondTargetSide (HalfEntry.entrySource
        B.brokenAssignment.index.second e) := by
    simp only [secondGapFinishSide]
    rw [he]
  have hposT : B.secondArcCut (B.secondGapFinishSide j) =
      B.secondTargetPos (HalfEntry.entrySource
        B.brokenAssignment.index.second e) := by
    rw [hfinish, (B.secondArcCut_target htTarget).1]
  have hposS : B.secondArcCut (B.secondTargetSide s) = B.secondTargetPos s :=
    (B.secondArcCut_target hsData.1).1
  have hstartLe : B.secondArcCut (B.secondGapStartSide j) ≤
      B.secondArcCut (B.secondTargetSide s) :=
    B.secondArc_isCutPath.cut.mono_le hsData.2.1
  have hadj : B.secondTargetPos s + 1 =
      B.secondTargetPos (HalfEntry.entrySource
        B.brokenAssignment.index.second e) := by
    rw [← hposS, ← hposT]
    omega
  have hltT : B.secondTargetPos (HalfEntry.entrySource
      B.brokenAssignment.index.second e) < B.secondArc.length := by
    have hend := (B.secondArc_targetComponent htTarget).2.1
    omega
  have hltS : B.secondTargetPos s + 1 < B.secondArc.length := by omega
  intro hEqLabel
  have hletterT := (B.secondArc_targetComponent htTarget).2.2.1
    (B.secondTargetPos (HalfEntry.entrySource
      B.brokenAssignment.index.second e)) le_rfl (by omega) hltT
  have hgoal : (B.secondArc[B.secondTargetPos s + 1]'hltS).IsCompOf
      (P.label s) := by
    rw [getElem_congr_idx hadj, hEqLabel]
    exact hletterT
  exact (B.secondArc_targetComponent hsData.1).2.2.2.2 hltS hgoal

/-! ## The full terminal exclusion -/

/-- The successor conjunct of `FirstGapArcBoundaryExclusion`, by the DGO case
split on where the letter after a retained arc target lies in the auxiliary
cycle.  Only the chord seam is left as an input. -/
theorem firstGapArcBoundaryExclusion_terminal_of_source
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j)
    (hseam : FirstGapArcChordSeam B j s) :
    ∀ hn : (B.firstGapLeft j).length +
        (B.firstArcCut (B.firstTargetSide s) -
          B.firstArcCut (B.firstGapStartSide j)) + 1 <
        (B.firstGapCycle j).length,
      ¬ ((B.firstGapCycle j)[
          (B.firstGapLeft j).length +
            (B.firstArcCut (B.firstTargetSide s) -
              B.firstArcCut (B.firstGapStartSide j)) + 1]'hn).IsCompOf
        (P.label s) := by
  classical
  intro hn hletter
  have hlocalComp : IsComp (P.label s)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j))
      (B.firstArcCut (B.firstTargetSide s) -
        B.firstArcCut (B.firstGapStartSide j))
      (B.firstArcCut (B.firstTargetSide s) -
        B.firstArcCut (B.firstGapStartSide j) + 1) :=
    B.firstGapArcSource_component j s hs
  by_cases hint : B.firstArcCut (B.firstTargetSide s) -
      B.firstArcCut (B.firstGapStartSide j) + 1 <
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)).length
  · have hco := (isCompOf_auxiliaryCycle_arc_iff (P.label s)
      (B.firstGapLeft j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)) (B.firstGapRight j)
      (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j))
      (B.firstArcCut (B.firstTargetSide s) -
        B.firstArcCut (B.firstGapStartSide j) + 1) hint hn).mp hletter
    exact hlocalComp.2.2.2.2 hint hco
  · have hbound := hlocalComp.2.1
    have hterminal : B.firstArcCut (B.firstTargetSide s) -
        B.firstArcCut (B.firstGapStartSide j) + 1 =
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length := by omega
    by_cases hnxt : HalfGap.nextEntry B.brokenAssignment.index.first j = none
    · have hright0 : (B.firstGapRight j).length = 0 := by
        simp only [firstGapRight]
        rw [hnxt]
        simp
      exact hseam hright0 hterminal hn hletter
    · obtain ⟨e, he'⟩ := Option.ne_none_iff_exists'.mp hnxt
      have he : HalfGap.nextEntry B.brokenAssignment.index.first j =
          some e := by simpa using he'
      by_cases hright : 0 < (B.firstGapRight j).length
      · have hlabel : P.label s ≠ B.firstGapLocalLabel j
            ((B.firstGapLeft j).length +
              (B.firstGapFinishSide j - B.firstGapStartSide j)) := by
          have hlab : B.firstGapLocalLabel j
              ((B.firstGapLeft j).length +
                (B.firstGapFinishSide j - B.firstGapStartSide j)) =
              P.label (HalfEntry.entrySource
                B.brokenAssignment.index.first e) := by
            simpa using B.firstGapLocalLabel_rightConnector j e he 0 hright
          rw [hlab]
          exact B.firstGapArcSource_label_ne_nextEntry j s hs e he hterminal
        exact firstGapArcBoundaryExclusion_terminal_of_rightConnector B j s hs
          e he hright hlabel hterminal hn hletter
      · exact hseam (by omega) hterminal hn hletter

/-- Wrapped counterpart of
`firstGapArcBoundaryExclusion_terminal_of_source`. -/
theorem secondGapArcBoundaryExclusion_terminal_of_source
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j)
    (hseam : SecondGapArcChordSeam B j s) :
    ∀ hn : (B.secondGapLeft j).length +
        (B.secondArcCut (B.secondTargetSide s) -
          B.secondArcCut (B.secondGapStartSide j)) + 1 <
        (B.secondGapCycle j).length,
      ¬ ((B.secondGapCycle j)[
          (B.secondGapLeft j).length +
            (B.secondArcCut (B.secondTargetSide s) -
              B.secondArcCut (B.secondGapStartSide j)) + 1]'hn).IsCompOf
        (P.label s) := by
  classical
  intro hn hletter
  have hlocalComp : IsComp (P.label s)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j))
      (B.secondArcCut (B.secondTargetSide s) -
        B.secondArcCut (B.secondGapStartSide j))
      (B.secondArcCut (B.secondTargetSide s) -
        B.secondArcCut (B.secondGapStartSide j) + 1) :=
    B.secondGapArcSource_component j s hs
  by_cases hint : B.secondArcCut (B.secondTargetSide s) -
      B.secondArcCut (B.secondGapStartSide j) + 1 <
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)).length
  · have hco := (isCompOf_auxiliaryCycle_arc_iff (P.label s)
      (B.secondGapLeft j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)) (B.secondGapRight j)
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j))
      (B.secondArcCut (B.secondTargetSide s) -
        B.secondArcCut (B.secondGapStartSide j) + 1) hint hn).mp hletter
    exact hlocalComp.2.2.2.2 hint hco
  · have hbound := hlocalComp.2.1
    have hterminal : B.secondArcCut (B.secondTargetSide s) -
        B.secondArcCut (B.secondGapStartSide j) + 1 =
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length := by omega
    by_cases hnxt : HalfGap.nextEntry B.brokenAssignment.index.second j = none
    · have hright0 : (B.secondGapRight j).length = 0 := by
        simp only [secondGapRight]
        rw [hnxt]
        simp
      exact hseam hright0 hterminal hn hletter
    · obtain ⟨e, he'⟩ := Option.ne_none_iff_exists'.mp hnxt
      have he : HalfGap.nextEntry B.brokenAssignment.index.second j =
          some e := by simpa using he'
      by_cases hright : 0 < (B.secondGapRight j).length
      · have hlabel : P.label s ≠ B.secondGapLocalLabel j
            ((B.secondGapLeft j).length +
              (B.secondGapFinishSide j - B.secondGapStartSide j)) := by
          have hlab : B.secondGapLocalLabel j
              ((B.secondGapLeft j).length +
                (B.secondGapFinishSide j - B.secondGapStartSide j)) =
              P.label (HalfEntry.entrySource
                B.brokenAssignment.index.second e) := by
            simpa using B.secondGapLocalLabel_rightConnector j e he 0 hright
          rw [hlab]
          exact B.secondGapArcSource_label_ne_nextEntry j s hs e he hterminal
        exact secondGapArcBoundaryExclusion_terminal_of_rightConnector B j s hs
          e he hright hlabel hterminal hn hletter
      · exact hseam (by omega) hterminal hn hletter

/-! ## Both endpoint exclusions, and the arc component field -/

/-- Both endpoint exclusions for a retained first-gap arc source, from the
chord seam alone. -/
theorem firstGapArcBoundaryExclusion_of_source
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j)
    (hseam : FirstGapArcChordSeam B j s) :
    FirstGapArcBoundaryExclusion B j s :=
  ⟨firstGapArcBoundaryExclusion_start_of_source B j s hs,
    firstGapArcBoundaryExclusion_terminal_of_source B j s hs hseam⟩

/-- Both endpoint exclusions for a retained wrapped-gap arc source. -/
theorem secondGapArcBoundaryExclusion_of_source
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j)
    (hseam : SecondGapArcChordSeam B j s) :
    SecondGapArcBoundaryExclusion B j s :=
  ⟨secondGapArcBoundaryExclusion_start_of_source B j s hs,
    secondGapArcBoundaryExclusion_terminal_of_source B j s hs hseam⟩

/-- The inherited arc component of a first-gap child, from the chord seam
alone.  This is the `arcComponent` field of `FirstGapComponentFamily`. -/
theorem firstGapArcSource_fullComponent_of_chordSeam
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j)
    (hseam : FirstGapArcChordSeam B j s) :
    IsComp (B.firstGapLocalLabel j
        ((B.firstGapLeft j).length +
          (B.firstTargetSide s - B.firstGapStartSide j)))
      (B.firstGapCycle j)
      (B.firstGapCut j ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j)))
      (B.firstGapCut j ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j) + 1)) :=
  firstGapArcSource_fullComponent_of_boundaryExclusion_auto B j s hs
    (firstGapArcBoundaryExclusion_of_source B j s hs hseam)

/-- The inherited arc component of a wrapped-gap child, from the chord seam
alone.  This is the `arcComponent` field of `SecondGapComponentFamily`. -/
theorem secondGapArcSource_fullComponent_of_chordSeam
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j)
    (hseam : SecondGapArcChordSeam B j s) :
    IsComp (B.secondGapLocalLabel j
        ((B.secondGapLeft j).length +
          (B.secondTargetSide s - B.secondGapStartSide j)))
      (B.secondGapCycle j)
      (B.secondGapCut j ((B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j)))
      (B.secondGapCut j ((B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j) + 1)) :=
  secondGapArcSource_fullComponent_of_boundaryExclusion_auto B j s hs
    (secondGapArcBoundaryExclusion_of_source B j s hs hseam)

/-! ## The chord seam of the final gap of a half -/

/-- DGO's terminal cycle `c_l` in the first half: a gap with no following
broken source runs to the end of the half arc, so the letter following the
retained target in the auxiliary cycle is the first letter of the reversed
chord, which is exactly the letter excluded by the half-word maximality clause
of a surviving source.  This discharges `FirstGapArcChordSeam` whenever the
gap is the last one. -/
theorem firstGapArcChordSeam_of_lastGap
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j)
    (hnone : HalfGap.nextEntry B.brokenAssignment.index.first j = none) :
    FirstGapArcChordSeam B j s := by
  classical
  intro hright0 hterminal hn hletter
  have hsData := Finset.mem_filter.mp hs
  have hfinish : B.firstGapFinishSide j = B.secondSide - B.firstSide + 1 := by
    simp only [firstGapFinishSide]
    rw [hnone]
  have hcutFull : B.firstArcCut (B.firstGapFinishSide j) =
      B.firstArc.length := by
    rw [hfinish]
    exact B.firstArc_isCutPath.cut.finish
  have harcLen : (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)).length =
      B.firstArcCut (B.firstGapFinishSide j) -
        B.firstArcCut (B.firstGapStartSide j) :=
    length_arcWord B.firstArc B.firstArcCut (le_of_eq hcutFull)
  have hposS : B.firstArcCut (B.firstTargetSide s) = B.firstTargetPos s :=
    (B.firstArcCut_target hsData.1).1
  have hstartLe : B.firstArcCut (B.firstGapStartSide j) ≤
      B.firstArcCut (B.firstTargetSide s) :=
    B.firstArc_isCutPath.cut.mono_le hsData.2.1
  have hend : B.firstTargetPos s + 1 = B.firstArc.length := by
    rw [← hposS]
    omega
  have hcycleLen : (B.firstGapCycle j).length =
      (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length +
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)).length := by
    simp only [firstGapCycle, auxiliaryCycleWord, List.length_append,
      OsinComponents.length_revWord]
  have hsegPos : 0 < (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j)).length := by omega
  have hchordStart : B.firstGapChordStart j = B.chord.length := by
    simp only [firstGapChordStart]
    rw [hnone]
  have hcfLe : B.firstGapChordFinish j ≤ B.chord.length :=
    B.firstGapChordFinish_le j
  have hcf : B.firstGapChordFinish j < B.chord.length := by
    rcases Nat.lt_or_ge (B.firstGapChordFinish j) B.chord.length with hlt | hge
    · exact hlt
    · exfalso
      have heq : B.firstGapChordFinish j = B.chord.length :=
        le_antisymm hcfLe hge
      rw [hchordStart, heq] at hsegPos
      simp [orientedSegment] at hsegPos
  have hn' : (B.firstGapLeft j).length +
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)).length +
      (B.firstGapRight j).length + 0 < (B.firstGapCycle j).length := by omega
  have hgetEq : (B.firstGapCycle j)[(B.firstGapLeft j).length +
        (B.firstArcCut (B.firstTargetSide s) -
          B.firstArcCut (B.firstGapStartSide j)) + 1]'hn =
      (B.firstGapCycle j)[(B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length + 0]'hn' :=
    getElem_congr_idx (by omega)
  rw [hgetEq] at hletter
  have hchordLetter := (isCompOf_auxiliaryCycle_chord_iff (P.label s)
    (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)) (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j)) 0 hsegPos hn').mp hletter
  have hrevPos : 0 < (revWord B.chord).length := by
    rw [OsinComponents.length_revWord]
    omega
  have hchordLetterRev : ((revWord B.chord)[0]'hrevPos).IsCompOf
      (P.label s) :=
    (isCompOf_head_orientedSegment_fromEnd (P.label s) B.chord hchordStart hcf
      hsegPos hrevPos).mp hchordLetter
  have hEnd : B.refinedCut (B.secondSide + 2) ≤ P.word.length := by
    rw [show B.refinedCut (B.secondSide + 2) = B.secondVertex by
      simp [refinedCut, splitPairCut_right]]
    exact B.secondVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
  have hArcLen : B.firstArc.length =
      B.refinedCut (B.secondSide + 2) - B.refinedCut (B.firstSide + 1) := by
    show (arcWord P.word B.refinedCut (B.firstSide + 1)
      (B.secondSide + 2)).length = _
    exact length_arcWord P.word B.refinedCut hEnd
  have hwordLen : B.firstWord.length =
      (B.refinedCut (B.secondSide + 2) - B.refinedCut (B.firstSide + 1)) +
        B.chord.length := by
    show (firstHalf P.word B.refinedCut (B.firstSide + 1) (B.secondSide + 2)
      B.chord).length = _
    exact length_firstHalf P.word B.refinedCut hEnd B.chord
  have hwordLt : (B.refinedCut (B.secondSide + 2) -
      B.refinedCut (B.firstSide + 1)) + 0 <
      (firstHalf P.word B.refinedCut (B.firstSide + 1) (B.secondSide + 2)
        B.chord).length := by
    rw [length_firstHalf P.word B.refinedCut hEnd]
    omega
  have hhalf := getElem_firstHalf_chord P.word B.refinedCut hEnd B.chord
    (j := 0) (by omega) hwordLt
  have hltWord : B.firstTargetPos s + 1 < B.firstWord.length := by
    rw [hwordLen]
    omega
  have hidxWord : B.firstTargetPos s + 1 =
      (B.refinedCut (B.secondSide + 2) - B.refinedCut (B.firstSide + 1)) + 0 := by
    omega
  have hfinal : B.firstWord[B.firstTargetPos s + 1]'hltWord =
      (revWord B.chord)[0]'hrevPos := by
    have h1 : B.firstWord[B.firstTargetPos s + 1]'hltWord =
        B.firstWord[(B.refinedCut (B.secondSide + 2) -
          B.refinedCut (B.firstSide + 1)) + 0]'(by rw [hwordLen]; omega) :=
      getElem_congr_idx hidxWord
    rw [h1]
    exact hhalf
  obtain ⟨hwordComp, -⟩ := B.firstGapArcSource_survives j s hs
  have hbad : (B.firstWord[B.firstTargetPos s + 1]'hltWord).IsCompOf
      (P.label s) := by
    rw [hfinal]
    exact hchordLetterRev
  exact hwordComp.2.2.2.2 hltWord hbad

/-- Wrapped counterpart of `firstGapArcChordSeam_of_lastGap`.  The wrapped
half closes with the chord read forwards, so the letter after the retained
target is the first letter of the chord itself. -/
theorem secondGapArcChordSeam_of_lastGap
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j)
    (hnone : HalfGap.nextEntry B.brokenAssignment.index.second j = none) :
    SecondGapArcChordSeam B j s := by
  classical
  intro hright0 hterminal hn hletter
  have hsData := Finset.mem_filter.mp hs
  have hfinish : B.secondGapFinishSide j =
      (n - B.secondSide) + B.firstSide + 1 := by
    simp only [secondGapFinishSide]
    rw [hnone]
  have hcutFull : B.secondArcCut (B.secondGapFinishSide j) =
      B.secondArc.length := by
    rw [hfinish]
    exact B.secondArc_isCutPath.cut.finish
  have harcLen : (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)).length =
      B.secondArcCut (B.secondGapFinishSide j) -
        B.secondArcCut (B.secondGapStartSide j) :=
    length_arcWord B.secondArc B.secondArcCut (le_of_eq hcutFull)
  have hposS : B.secondArcCut (B.secondTargetSide s) = B.secondTargetPos s :=
    (B.secondArcCut_target hsData.1).1
  have hstartLe : B.secondArcCut (B.secondGapStartSide j) ≤
      B.secondArcCut (B.secondTargetSide s) :=
    B.secondArc_isCutPath.cut.mono_le hsData.2.1
  have hend : B.secondTargetPos s + 1 = B.secondArc.length := by
    rw [← hposS]
    omega
  have hcycleLen : (B.secondGapCycle j).length =
      (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length +
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)).length := by
    simp only [secondGapCycle, auxiliaryCycleWord, List.length_append,
      OsinComponents.length_revWord]
  have hsegPos : 0 < (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)).length := by omega
  have hchordStart : B.secondGapChordStart j = 0 := by
    simp only [secondGapChordStart]
    rw [hnone]
  have hsegLe : (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)).length ≤ B.chord.length := by
    rw [hchordStart, orientedSegment, if_pos (Nat.zero_le _)]
    simp
  have hchordPos : 0 < B.chord.length := by omega
  have hn' : (B.secondGapLeft j).length +
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)).length +
      (B.secondGapRight j).length + 0 < (B.secondGapCycle j).length := by omega
  have hgetEq : (B.secondGapCycle j)[(B.secondGapLeft j).length +
        (B.secondArcCut (B.secondTargetSide s) -
          B.secondArcCut (B.secondGapStartSide j)) + 1]'hn =
      (B.secondGapCycle j)[(B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length + 0]'hn' :=
    getElem_congr_idx (by omega)
  rw [hgetEq] at hletter
  have hchordLetter := (isCompOf_auxiliaryCycle_chord_iff (P.label s)
    (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)) (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)) 0 hsegPos hn').mp hletter
  have hchordHead : (B.chord[0]'hchordPos).IsCompOf (P.label s) :=
    (isCompOf_head_orientedSegment_fromStart (P.label s) B.chord hchordStart
      hsegPos hchordPos).mp hchordLetter
  have hleftCut : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  have hrightCut : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have hsecondLe : B.secondVertex ≤ P.word.length :=
    B.secondVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
  have hfirstLe : B.firstVertex ≤ P.word.length :=
    B.split_vertices_ordered.trans hsecondLe
  have hEndA : B.refinedCut (B.firstSide + 1) ≤ P.word.length := by
    rw [hleftCut]
    exact hfirstLe
  have hArcLen : B.secondArc.length =
      (P.word.length - B.refinedCut (B.secondSide + 2)) +
        B.refinedCut (B.firstSide + 1) := by
    rw [hleftCut, hrightCut]
    show (P.word.drop B.secondVertex ++ P.word.take B.firstVertex).length = _
    rw [List.length_append, List.length_drop, List.length_take]
    omega
  have hwordLen : B.secondWord.length =
      (P.word.length - B.refinedCut (B.secondSide + 2)) +
        B.refinedCut (B.firstSide + 1) + B.chord.length := by
    show (secondHalf P.word B.refinedCut (B.firstSide + 1) (B.secondSide + 2)
      B.chord).length = _
    exact length_secondHalf P.word B.refinedCut hEndA B.chord
  have hwordLt : (P.word.length - B.refinedCut (B.secondSide + 2)) +
      B.refinedCut (B.firstSide + 1) + 0 <
      (secondHalf P.word B.refinedCut (B.firstSide + 1) (B.secondSide + 2)
        B.chord).length := by
    rw [length_secondHalf P.word B.refinedCut hEndA]
    omega
  have hhalf := getElem_secondHalf_chord P.word B.refinedCut hEndA B.chord
    (j := 0) hchordPos hwordLt
  have hltWord : B.secondTargetPos s + 1 < B.secondWord.length := by
    rw [hwordLen]
    omega
  have hidxWord : B.secondTargetPos s + 1 =
      (P.word.length - B.refinedCut (B.secondSide + 2)) +
        B.refinedCut (B.firstSide + 1) + 0 := by
    omega
  have hfinal : B.secondWord[B.secondTargetPos s + 1]'hltWord =
      B.chord[0]'hchordPos := by
    have h1 : B.secondWord[B.secondTargetPos s + 1]'hltWord =
        B.secondWord[(P.word.length - B.refinedCut (B.secondSide + 2)) +
          B.refinedCut (B.firstSide + 1) + 0]'(by rw [hwordLen]; omega) :=
      getElem_congr_idx hidxWord
    rw [h1]
    exact hhalf
  obtain ⟨hwordComp, -⟩ := B.secondGapArcSource_survives j s hs
  have hbad : (B.secondWord[B.secondTargetPos s + 1]'hltWord).IsCompOf
      (P.label s) := by
    rw [hfinal]
    exact hchordHead
  exact hwordComp.2.2.2.2 hltWord hbad

/-! ## Partner edges are maximal components of the geodesic chord -/

/-- The chord partner of a broken first-half source is its own maximal
component of the chord, because the chord is geodesic. -/
theorem firstPartner_chord_isComp
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    IsComp (P.label s) B.chord (B.brokenAssignment.first.partner s)
      (B.brokenAssignment.first.partner s + 1) :=
  isComp_of_isCompOf_geodesic D (P.label s) B.chord_geodesic
    (B.brokenAssignment.first.partner_lt s hs)
    (B.firstPartner_chordLetter_label s hs)

/-- The chord partner of a broken wrapped-half source is its own maximal
component of the chord. -/
theorem secondPartner_chord_isComp
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    IsComp (P.label s) B.chord (B.brokenAssignment.second.partner s)
      (B.brokenAssignment.second.partner s + 1) :=
  isComp_of_isCompOf_geodesic D (P.label s) B.chord_geodesic
    (B.brokenAssignment.second.partner_lt s hs)
    (B.secondPartner_chordLetter_label s hs)

/-! ## The exact residue of the arc component field -/

/-- Everything in `FirstGapArcChordSeam` except one case is now proved: a gap
with no following broken source is the last cycle of the half, and a gap with
a nonempty right connector never reaches the chord at that seam.  What is left
is an interior gap whose right connector degenerates to the empty path, which
is where DGO invoke "`p_i ∈ I₁ \ J₁` can not be connected to a component of
`t`". -/
theorem firstGapArcChordSeam_of_degenerateSeam
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j)
    (hres : ∀ e : Fin B.brokenAssignment.index.first.sources.length,
      HalfGap.nextEntry B.brokenAssignment.index.first j = some e →
      (B.firstGapRight j).length = 0 → FirstGapArcChordSeam B j s) :
    FirstGapArcChordSeam B j s := by
  classical
  by_cases hnone : HalfGap.nextEntry B.brokenAssignment.index.first j = none
  · exact firstGapArcChordSeam_of_lastGap B j s hs hnone
  · obtain ⟨e, he'⟩ := Option.ne_none_iff_exists'.mp hnone
    have he : HalfGap.nextEntry B.brokenAssignment.index.first j = some e := by
      simpa using he'
    by_cases hright : 0 < (B.firstGapRight j).length
    · exact firstGapArcChordSeam_of_rightConnector B j s hright
    · exact hres e he (by omega)

/-- Wrapped counterpart of `firstGapArcChordSeam_of_degenerateSeam`. -/
theorem secondGapArcChordSeam_of_degenerateSeam
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j)
    (hres : ∀ e : Fin B.brokenAssignment.index.second.sources.length,
      HalfGap.nextEntry B.brokenAssignment.index.second j = some e →
      (B.secondGapRight j).length = 0 → SecondGapArcChordSeam B j s) :
    SecondGapArcChordSeam B j s := by
  classical
  by_cases hnone : HalfGap.nextEntry B.brokenAssignment.index.second j = none
  · exact secondGapArcChordSeam_of_lastGap B j s hs hnone
  · obtain ⟨e, he'⟩ := Option.ne_none_iff_exists'.mp hnone
    have he : HalfGap.nextEntry B.brokenAssignment.index.second j = some e := by
      simpa using he'
    by_cases hright : 0 < (B.secondGapRight j).length
    · exact secondGapArcChordSeam_of_rightConnector B j s hright
    · exact hres e he (by omega)

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
