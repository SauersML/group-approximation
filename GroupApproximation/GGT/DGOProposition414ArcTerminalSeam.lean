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

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
