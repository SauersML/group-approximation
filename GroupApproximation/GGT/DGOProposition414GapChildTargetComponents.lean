import GroupApproximation.GGT.DGOProposition414GapChordComponents
import GroupApproximation.GGT.DGOProposition414GapConnectorComponents
import GroupApproximation.GGT.OsinTheorem54SepDistSuffix

/-!
# Target components in the balanced-split gap children

This module places the inherited-arc and selected-chord components at their
exact auxiliary-cycle cut coordinates.  The interior cases are the direct
type-(1) and type-(4) component transfers in the proof of Dahmani--Guirardel--
Osin Proposition 4.14.  The endpoint cases are handled separately by the
adjacent broken-component dictionaries.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- The local side of an inherited first-gap target cuts at its shifted
component position in the auxiliary word. -/
theorem firstGapArcSource_auxiliaryCut
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j) :
    auxiliaryCycleCut (B.firstGapLeft j)
        (B.firstGapFinishSide j - B.firstGapStartSide j)
        (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
          B.firstArcCut (B.firstGapStartSide j))
        (B.firstGapRight j)
        ((B.firstGapLeft j).length +
          (B.firstTargetSide s - B.firstGapStartSide j)) =
      (B.firstGapLeft j).length +
        (B.firstArcCut (B.firstTargetSide s) -
          B.firstArcCut (B.firstGapStartSide j)) := by
  have hsData := Finset.mem_filter.mp hs
  let r := B.firstTargetSide s - B.firstGapStartSide j
  have hr : r < B.firstGapFinishSide j - B.firstGapStartSide j := by
    dsimp [r]
    omega
  have hrEq : B.firstGapStartSide j + r = B.firstTargetSide s := by
    dsimp [r]
    omega
  have hside := B.firstGap_side_order j
  have hlast := B.firstGapFinishSide_le j
  let restricted := IsCutPath.arcWord B.firstArc_isCutPath hside hlast
  have hcut := auxiliaryCycleCut_arc (B.firstGapLeft j)
    (B.firstGapRight j) restricted.cut (r := r) hr.le
  change auxiliaryCycleCut (B.firstGapLeft j)
      (B.firstGapFinishSide j - B.firstGapStartSide j)
      (fun x => B.firstArcCut (B.firstGapStartSide j + x) -
        B.firstArcCut (B.firstGapStartSide j))
      (B.firstGapRight j) ((B.firstGapLeft j).length + r) = _
  rw [hcut, hrEq]

/-- Wrapped-half counterpart of `firstGapArcSource_auxiliaryCut`. -/
theorem secondGapArcSource_auxiliaryCut
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j) :
    auxiliaryCycleCut (B.secondGapLeft j)
        (B.secondGapFinishSide j - B.secondGapStartSide j)
        (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
          B.secondArcCut (B.secondGapStartSide j))
        (B.secondGapRight j)
        ((B.secondGapLeft j).length +
          (B.secondTargetSide s - B.secondGapStartSide j)) =
      (B.secondGapLeft j).length +
        (B.secondArcCut (B.secondTargetSide s) -
          B.secondArcCut (B.secondGapStartSide j)) := by
  have hsData := Finset.mem_filter.mp hs
  let r := B.secondTargetSide s - B.secondGapStartSide j
  have hr : r < B.secondGapFinishSide j - B.secondGapStartSide j := by
    dsimp [r]
    omega
  have hrEq : B.secondGapStartSide j + r = B.secondTargetSide s := by
    dsimp [r]
    omega
  have hside := B.secondGap_side_order j
  have hlast := B.secondGapFinishSide_le j
  let restricted := IsCutPath.arcWord B.secondArc_isCutPath hside hlast
  have hcut := auxiliaryCycleCut_arc (B.secondGapLeft j)
    (B.secondGapRight j) restricted.cut (r := r) hr.le
  change auxiliaryCycleCut (B.secondGapLeft j)
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (fun x => B.secondArcCut (B.secondGapStartSide j + x) -
        B.secondArcCut (B.secondGapStartSide j))
      (B.secondGapRight j) ((B.secondGapLeft j).length + r) = _
  rw [hcut, hrEq]

/-- A selected chord edge cuts at its shifted oriented-segment position in a
first-gap auxiliary word. -/
theorem firstGapChordSource_auxiliaryCut
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) :
    auxiliaryCycleCut (B.firstGapLeft j)
        (B.firstGapFinishSide j - B.firstGapStartSide j)
        (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
          B.firstArcCut (B.firstGapStartSide j))
        (B.firstGapRight j)
        (B.firstGapChordTargetIndex j
          (B.brokenAssignment.second.partner s)) =
      (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length +
        orientedEdgeIndex (B.firstGapChordStart j)
          (B.firstGapChordFinish j)
          (B.brokenAssignment.second.partner s) := by
  have hside := B.firstGap_side_order j
  have hlast := B.firstGapFinishSide_le j
  let restricted := IsCutPath.arcWord B.firstArc_isCutPath hside hlast
  have hcut := auxiliaryCycleCut_chord (B.firstGapLeft j)
    (B.firstGapRight j) restricted.cut
    (r := orientedEdgeIndex (B.firstGapChordStart j)
      (B.firstGapChordFinish j) (B.brokenAssignment.second.partner s))
  unfold firstGapChordTargetIndex auxiliaryChordTargetIndex
  simpa only using hcut

/-- Wrapped-half counterpart of `firstGapChordSource_auxiliaryCut`. -/
theorem secondGapChordSource_auxiliaryCut
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) :
    auxiliaryCycleCut (B.secondGapLeft j)
        (B.secondGapFinishSide j - B.secondGapStartSide j)
        (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
          B.secondArcCut (B.secondGapStartSide j))
        (B.secondGapRight j)
        (B.secondGapChordTargetIndex j
          (B.brokenAssignment.first.partner s)) =
      (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length +
        orientedEdgeIndex (B.secondGapChordStart j)
          (B.secondGapChordFinish j)
          (B.brokenAssignment.first.partner s) := by
  have hside := B.secondGap_side_order j
  have hlast := B.secondGapFinishSide_le j
  let restricted := IsCutPath.arcWord B.secondArc_isCutPath hside hlast
  have hcut := auxiliaryCycleCut_chord (B.secondGapLeft j)
    (B.secondGapRight j) restricted.cut
    (r := orientedEdgeIndex (B.secondGapChordStart j)
      (B.secondGapChordFinish j) (B.brokenAssignment.first.partner s))
  unfold secondGapChordTargetIndex auxiliaryChordTargetIndex
  simpa only using hcut

/-- An inherited first-gap target which is interior to the retained arc is a
maximal component of the complete auxiliary word. -/
theorem firstGapArcSource_cycleComponent_of_interior
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j)
    (hstart : 1 ≤ B.firstArcCut (B.firstTargetSide s) -
      B.firstArcCut (B.firstGapStartSide j))
    (hfinish : B.firstArcCut (B.firstTargetSide s) -
        B.firstArcCut (B.firstGapStartSide j) + 1 <
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)).length) :
    IsComp
      (B.firstGapLocalLabel j ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j)))
      (auxiliaryCycleWord (B.firstGapLeft j)
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j))
        (B.firstGapRight j)
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)))
      ((B.firstGapLeft j).length +
        (B.firstArcCut (B.firstTargetSide s) -
          B.firstArcCut (B.firstGapStartSide j)))
      ((B.firstGapLeft j).length +
        (B.firstArcCut (B.firstTargetSide s) -
          B.firstArcCut (B.firstGapStartSide j)) + 1) := by
  rw [B.firstGapLocalLabel_arc j s hs]
  exact isComp_auxiliaryCycle_arc (P.label s) (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)) (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j))
    (B.firstGapArcSource_component j s hs) hstart hfinish

/-- Wrapped-half counterpart of
`firstGapArcSource_cycleComponent_of_interior`. -/
theorem secondGapArcSource_cycleComponent_of_interior
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j)
    (hstart : 1 ≤ B.secondArcCut (B.secondTargetSide s) -
      B.secondArcCut (B.secondGapStartSide j))
    (hfinish : B.secondArcCut (B.secondTargetSide s) -
        B.secondArcCut (B.secondGapStartSide j) + 1 <
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)).length) :
    IsComp
      (B.secondGapLocalLabel j ((B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j)))
      (auxiliaryCycleWord (B.secondGapLeft j)
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j))
        (B.secondGapRight j)
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)))
      ((B.secondGapLeft j).length +
        (B.secondArcCut (B.secondTargetSide s) -
          B.secondArcCut (B.secondGapStartSide j)))
      ((B.secondGapLeft j).length +
        (B.secondArcCut (B.secondTargetSide s) -
          B.secondArcCut (B.secondGapStartSide j)) + 1) := by
  rw [B.secondGapLocalLabel_arc j s hs]
  exact isComp_auxiliaryCycle_arc (P.label s) (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)) (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j))
    (B.secondGapArcSource_component j s hs) hstart hfinish

/-- A selected chord target which is interior to its oriented segment is a
maximal component of the first-gap auxiliary word. -/
theorem firstGapChordSource_cycleComponent_of_interior
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapChordSources j)
    (hstart : 1 ≤ orientedEdgeIndex (B.firstGapChordStart j)
      (B.firstGapChordFinish j) (B.brokenAssignment.second.partner s))
    (hfinish : orientedEdgeIndex (B.firstGapChordStart j)
        (B.firstGapChordFinish j) (B.brokenAssignment.second.partner s) + 1 <
      (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j)).length) :
    IsComp (B.firstGapLocalLabel j (B.firstGapChordTargetIndex j
        (B.brokenAssignment.second.partner s)))
      (auxiliaryCycleWord (B.firstGapLeft j)
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j))
        (B.firstGapRight j)
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)))
      ((B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length +
        orientedEdgeIndex (B.firstGapChordStart j)
          (B.firstGapChordFinish j) (B.brokenAssignment.second.partner s))
      ((B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length +
        orientedEdgeIndex (B.firstGapChordStart j)
          (B.firstGapChordFinish j) (B.brokenAssignment.second.partner s) + 1) := by
  rw [B.firstGapLocalLabel_chord j s hs]
  exact isComp_auxiliaryCycle_chord (P.label s) (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)) (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j))
    (B.firstGapChordSource_segmentComponent j s hs) hstart hfinish

/-- Wrapped-half counterpart of
`firstGapChordSource_cycleComponent_of_interior`. -/
theorem secondGapChordSource_cycleComponent_of_interior
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapChordSources j)
    (hstart : 1 ≤ orientedEdgeIndex (B.secondGapChordStart j)
      (B.secondGapChordFinish j) (B.brokenAssignment.first.partner s))
    (hfinish : orientedEdgeIndex (B.secondGapChordStart j)
        (B.secondGapChordFinish j) (B.brokenAssignment.first.partner s) + 1 <
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j)).length) :
    IsComp (B.secondGapLocalLabel j (B.secondGapChordTargetIndex j
        (B.brokenAssignment.first.partner s)))
      (auxiliaryCycleWord (B.secondGapLeft j)
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j))
        (B.secondGapRight j)
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)))
      ((B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length +
        orientedEdgeIndex (B.secondGapChordStart j)
          (B.secondGapChordFinish j) (B.brokenAssignment.first.partner s))
      ((B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length +
        orientedEdgeIndex (B.secondGapChordStart j)
          (B.secondGapChordFinish j) (B.brokenAssignment.first.partner s) + 1) := by
  rw [B.secondGapLocalLabel_chord j s hs]
  exact isComp_auxiliaryCycle_chord (P.label s) (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)) (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j))
    (B.secondGapChordSource_segmentComponent j s hs) hstart hfinish

/-! ## Boundary-aware adapters

The next four lemmas expose the only hypotheses left when a selected edge is
at an end of its retained path.  They are the exact boundary clauses of the
general component-transfer theorem; later gap-family constructions discharge
them from the adjacent broken source or the surviving half component.
-/

theorem firstGapArcSource_cycleComponent_of_boundary
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j)
    (hstart : ∀ t : ℕ,
      (B.firstGapLeft j).length +
          (B.firstArcCut (B.firstTargetSide s) -
            B.firstArcCut (B.firstGapStartSide j)) = t + 1 →
      ∀ ht : t <
        (auxiliaryCycleWord (B.firstGapLeft j)
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)) (B.firstGapRight j)
          (orientedSegment B.chord (B.firstGapChordStart j)
            (B.firstGapChordFinish j))).length,
      ¬ ((auxiliaryCycleWord (B.firstGapLeft j)
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)) (B.firstGapRight j)
          (orientedSegment B.chord (B.firstGapChordStart j)
            (B.firstGapChordFinish j)))[t]'ht).IsCompOf (P.label s))
    (hend : ∀ hn :
      (B.firstGapLeft j).length +
          (B.firstArcCut (B.firstTargetSide s) -
            B.firstArcCut (B.firstGapStartSide j)) + 1 <
        (auxiliaryCycleWord (B.firstGapLeft j)
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)) (B.firstGapRight j)
          (orientedSegment B.chord (B.firstGapChordStart j)
            (B.firstGapChordFinish j))).length,
      ¬ ((auxiliaryCycleWord (B.firstGapLeft j)
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)) (B.firstGapRight j)
          (orientedSegment B.chord (B.firstGapChordStart j)
            (B.firstGapChordFinish j)))[
          (B.firstGapLeft j).length +
            (B.firstArcCut (B.firstTargetSide s) -
              B.firstArcCut (B.firstGapStartSide j)) + 1]'hn).IsCompOf
        (P.label s)) :
    IsComp (P.label s)
      (auxiliaryCycleWord (B.firstGapLeft j)
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)) (B.firstGapRight j)
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)))
      ((B.firstGapLeft j).length +
        (B.firstArcCut (B.firstTargetSide s) -
          B.firstArcCut (B.firstGapStartSide j)))
      ((B.firstGapLeft j).length +
        (B.firstArcCut (B.firstTargetSide s) -
          B.firstArcCut (B.firstGapStartSide j)) + 1) := by
  have hcomp := B.firstGapArcSource_component j s hs
  let cycle := auxiliaryCycleWord (B.firstGapLeft j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)) (B.firstGapRight j)
      (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j))
  have hseg : (cycle.drop (B.firstGapLeft j).length).take
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)).length =
      arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j) := by
    simp [cycle, auxiliaryCycleWord, OsinComponents.length_revWord]
  have hcomp' : IsComp (P.label s)
      (cycle.drop (B.firstGapLeft j).length |>.take
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length)
      (B.firstArcCut (B.firstTargetSide s) -
        B.firstArcCut (B.firstGapStartSide j))
      (B.firstArcCut (B.firstTargetSide s) -
        B.firstArcCut (B.firstGapStartSide j) + 1) := by
    rw [hseg]
    exact hcomp
  have hsegment := OsinComponents.isComp_of_isComp_segment_general (P.label s)
    cycle hcomp' hstart hend (by
      simp [cycle, auxiliaryCycleWord, OsinComponents.length_revWord])
  simpa only [cycle, B.firstGapLocalLabel_arc j s hs,
    B.firstGapArcSource_auxiliaryCut j s hs, Nat.add_assoc] using hsegment

theorem secondGapArcSource_cycleComponent_of_boundary
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j)
    (hstart : ∀ t : ℕ,
      (B.secondGapLeft j).length +
          (B.secondArcCut (B.secondTargetSide s) -
            B.secondArcCut (B.secondGapStartSide j)) = t + 1 →
      ∀ ht : t <
        (auxiliaryCycleWord (B.secondGapLeft j)
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)) (B.secondGapRight j)
          (orientedSegment B.chord (B.secondGapChordStart j)
            (B.secondGapChordFinish j))).length,
      ¬ ((auxiliaryCycleWord (B.secondGapLeft j)
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)) (B.secondGapRight j)
          (orientedSegment B.chord (B.secondGapChordStart j)
            (B.secondGapChordFinish j)))[t]'ht).IsCompOf (P.label s))
    (hend : ∀ hn :
      (B.secondGapLeft j).length +
          (B.secondArcCut (B.secondTargetSide s) -
            B.secondArcCut (B.secondGapStartSide j)) + 1 <
        (auxiliaryCycleWord (B.secondGapLeft j)
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)) (B.secondGapRight j)
          (orientedSegment B.chord (B.secondGapChordStart j)
            (B.secondGapChordFinish j))).length,
      ¬ ((auxiliaryCycleWord (B.secondGapLeft j)
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)) (B.secondGapRight j)
          (orientedSegment B.chord (B.secondGapChordStart j)
            (B.secondGapChordFinish j)))[
          (B.secondGapLeft j).length +
            (B.secondArcCut (B.secondTargetSide s) -
              B.secondArcCut (B.secondGapStartSide j)) + 1]'hn).IsCompOf
        (P.label s)) :
    IsComp (P.label s)
      (auxiliaryCycleWord (B.secondGapLeft j)
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)) (B.secondGapRight j)
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)))
      ((B.secondGapLeft j).length +
        (B.secondArcCut (B.secondTargetSide s) -
          B.secondArcCut (B.secondGapStartSide j)))
      ((B.secondGapLeft j).length +
        (B.secondArcCut (B.secondTargetSide s) -
          B.secondArcCut (B.secondGapStartSide j)) + 1) := by
  have hcomp := B.secondGapArcSource_component j s hs
  let cycle := auxiliaryCycleWord (B.secondGapLeft j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)) (B.secondGapRight j)
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j))
  have hseg : (cycle.drop (B.secondGapLeft j).length).take
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)).length =
      arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j) := by
    simp [cycle, auxiliaryCycleWord, OsinComponents.length_revWord]
  have hcomp' : IsComp (P.label s)
      (cycle.drop (B.secondGapLeft j).length |>.take
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length)
      (B.secondArcCut (B.secondTargetSide s) -
        B.secondArcCut (B.secondGapStartSide j))
      (B.secondArcCut (B.secondTargetSide s) -
        B.secondArcCut (B.secondGapStartSide j) + 1) := by
    rw [hseg]
    exact hcomp
  have hsegment := OsinComponents.isComp_of_isComp_segment_general (P.label s)
    cycle hcomp' hstart hend (by
      simp [cycle, auxiliaryCycleWord, OsinComponents.length_revWord])
  simpa only [cycle, B.secondGapLocalLabel_arc j s hs,
    B.secondGapArcSource_auxiliaryCut j s hs, Nat.add_assoc] using hsegment

/-
/-! The following seam lemma is the first concrete endpoint instance.  Its
right boundary uses the surviving half-word component, while a left boundary
uses the preceding broken entry and its connector label. -/

theorem firstGapArcSource_cycleComponent
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j) :
    IsComp
      (B.firstGapLocalLabel j ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j)))
      (auxiliaryCycleWord (B.firstGapLeft j)
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)) (B.firstGapRight j)
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)))
      (auxiliaryCycleCut (B.firstGapLeft j)
        (B.firstGapFinishSide j - B.firstGapStartSide j)
        (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
          B.firstArcCut (B.firstGapStartSide j)) (B.firstGapRight j)
        ((B.firstGapLeft j).length +
          (B.firstTargetSide s - B.firstGapStartSide j)))
      (auxiliaryCycleCut (B.firstGapLeft j)
        (B.firstGapFinishSide j - B.firstGapStartSide j)
        (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
          B.firstArcCut (B.firstGapStartSide j)) (B.firstGapRight j)
        ((B.firstGapLeft j).length +
          (B.firstTargetSide s - B.firstGapStartSide j) + 1)) := by
  have hsData := Finset.mem_filter.mp hs
  let i := B.firstArcCut (B.firstTargetSide s) -
    B.firstArcCut (B.firstGapStartSide j)
  let cycle := auxiliaryCycleWord (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)) (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j))
  have hcycleLen : cycle.length =
      (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length +
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)).length := by
    simp [cycle, auxiliaryCycleWord, OsinComponents.length_revWord,
      Nat.add_assoc]
  have hleftArc : (B.firstGapLeft j).length + i ≤
      (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length := by
    have hcut := B.firstArc_isCutPath.cut.mono_le
      hsData.2.1
    have hcut' := B.firstArc_isCutPath.cut.mono_le
      (Nat.succ_le_iff.mpr hsData.2.2)
    have hlen := length_arcWord B.firstArc B.firstArcCut
      (B.firstArc_isCutPath.cut.le_length (B.firstGapFinishSide_le j))
    dsimp [i]
    rw [hlen]
    omega
  have hlocalComp : IsComp (P.label s)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)) i (i + 1) := by
    simpa only [i] using B.firstGapArcSource_component j s hs
  have hstart : ∀ t : ℕ,
      (B.firstGapLeft j).length + i = t + 1 →
      ∀ ht : t < cycle.length, ¬ (cycle[t]'ht).IsCompOf (P.label s) := by
    intro t hteq ht
    by_cases hi : 0 < i
    · have htArc : t - (B.firstGapLeft j).length <
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)).length := by omega
      have htEq : t = (B.firstGapLeft j).length + (t -
          (B.firstGapLeft j).length) := by omega
      have hletter := (isComp_auxiliaryCycle_arc_iff (P.label s)
        (B.firstGapLeft j)
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)) (B.firstGapRight j)
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)) (t - (B.firstGapLeft j).length)
        htArc (by omega)).mp (by simpa [cycle, htEq] using ‹(cycle[t]'ht).IsCompOf (P.label s)›)
      have hpre := hlocalComp.2.2.2.1 (i - 1) (by omega) (by omega) htArc
      rw [show t - (B.firstGapLeft j).length = i - 1 by omega] at hletter
      exact hpre (i - 1) (by omega) htArc hletter
    · have hi0 : i = 0 := by omega
      subst i
      by_cases hp : HalfGap.previousEntry B.brokenAssignment.index.first j = none
      · have hleft0 : (B.firstGapLeft j).length = 0 := by
          simp [firstGapLeft, hp]
        omega
      · obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hp
        have heq : HalfGap.previousEntry B.brokenAssignment.index.first j = some e := by
          simpa using he
        have het : e.val < B.brokenAssignment.index.first.sources.length := e.isLt
        have htleft : t < (B.firstGapLeft j).length := by omega
        have hconn := B.firstGap_leftConnector_isCompOf j e heq t htleft (by
          rw [cycle] at ht
          simpa [auxiliaryCycleWord, OsinComponents.length_revWord] using ht)
        have hconnLabel := B.firstGapLocalLabel_leftConnector j e heq t htleft
        have hEqLabel : P.label s =
            P.label (HalfEntry.entrySource B.brokenAssignment.index.first e) :=
          eq_of_isCompOf_of_isCompOf hconn hconnLabel
        have heSrc := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
        have heTarget := (mem_brokenSet_iff.mp heSrc).1
        have hprevComp := B.firstArc_targetComponent heTarget
        have hprevSide : B.firstGapStartSide j =
            B.firstTargetSide (HalfEntry.entrySource
              B.brokenAssignment.index.first e) + 1 := by
          simp only [firstGapStartSide]
          rw [heq]
        have hprevPos : B.firstArcCut
            (B.firstTargetSide (HalfEntry.entrySource
              B.brokenAssignment.index.first e)) + 1 =
            B.firstArcCut (B.firstGapStartSide j) := by
          rw [hprevSide]
          rw [← hprevSide, (B.firstArcCut_target heTarget).2]
        have hprevLetter :
            (B.firstArc[B.firstArcCut (B.firstTargetSide
              (HalfEntry.entrySource B.brokenAssignment.index.first e))]'(by
                exact B.firstArc_isCutPath.cut.le_length
                  (B.firstTargetSide_lt heTarget).le)).IsCompOf
              (P.label (HalfEntry.entrySource
                B.brokenAssignment.index.first e)) :=
          hprevComp.2.2.1 _ le_rfl (by omega) _
        have hprevLabel :
            (B.firstArc[B.firstArcCut (B.firstTargetSide
              (HalfEntry.entrySource B.brokenAssignment.index.first e))]'(by
                exact B.firstArc_isCutPath.cut.le_length
                  (B.firstTargetSide_lt heTarget).le)).IsCompOf (P.label s) := by
          simpa only [hEqLabel] using hprevLetter
        have hparent := B.firstArc_targetComponent hsData.1
        have hidx : B.firstArcCut (B.firstTargetSide
              (HalfEntry.entrySource B.brokenAssignment.index.first e)) =
            B.firstArcCut (B.firstTargetSide s) - 1 := by
          have hcur : B.firstArcCut (B.firstTargetSide s) =
              B.firstArcCut (B.firstGapStartSide j) := by
            exact (B.firstArcCut_target hsData.1).1.trans (by simp [hi0])
          rw [hcur, ← hprevPos]
          omega
        apply hparent.2.2.2.1
          (B.firstArcCut (B.firstTargetSide s) - 1) (by omega) _ hprevLabel
    · exact (by omega)
  have hend : ∀ hn :
      (B.firstGapLeft j).length + i + 1 < cycle.length,
      ¬ (cycle[(B.firstGapLeft j).length + i + 1]'hn).IsCompOf (P.label s) := by
    intro hn hletter
    have hlenArc := length_arcWord B.firstArc B.firstArcCut
      (B.firstArc_isCutPath.cut.le_length (B.firstGapFinishSide_le j))
    by_cases hiend : i + 1 <
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length
    · have hco := (isComp_auxiliaryCycle_arc_iff (P.label s)
        (B.firstGapLeft j)
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)) (B.firstGapRight j)
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)) (i + 1) hiend (by omega)).mp (by
            simpa [cycle] using hletter)
      exact hlocalComp.2.2.2.2 _ (by omega) hiend hco
    · have hiEq : i + 1 =
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length := by omega
      have hcurCut : B.firstArcCut (B.firstTargetSide s) + 1 =
          B.firstArcCut (B.firstGapFinishSide j) := by
        rw [← (B.firstArcCut_target hsData.1).2]
        have := B.firstArc_isCutPath.cut.mono_le
          (Nat.succ_le_iff.mpr hsData.2.2)
        omega
      by_cases hnxt : HalfGap.nextEntry B.brokenAssignment.index.first j = none
      · have hsurv := B.firstGapArcSource_survives j s hs
        have hwordComp := hsurv.1
        have hwordPost := hwordComp.2.2.2.2
        have hwordLen : B.firstWord.length =
            B.firstArc.length + B.chord.length := by
          simp [BalancedSplitData.firstWord, firstHalf, Nat.add_assoc]
        have hauxEq : (cycle[(B.firstGapLeft j).length + i + 1]'hn) =
            B.firstWord[B.firstTargetPos s + 1]'(by
              rw [← (B.firstArcCut_target hsData.1).2]
              omega) := by
          simp [cycle, auxiliaryCycleWord, OsinComponents.length_revWord,
            hwordComp, hwordLen, hiEq]
          omega
        rw [hauxEq] at hletter
        exact hwordPost _ (by omega) hletter
      · obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hnxt
        have heq : HalfGap.nextEntry B.brokenAssignment.index.first j = some e := by
          simpa using he
        have heSrc := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
        have heTarget := (mem_brokenSet_iff.mp heSrc).1
        have hright : B.firstGapFinishSide j =
            B.firstTargetSide (HalfEntry.entrySource
              B.brokenAssignment.index.first e) := by
          simp only [firstGapFinishSide]
          rw [heq]
        have hrightPos : 0 < (B.firstGapRight j).length := by
          have := B.firstGapRight_length_le_one j
          omega
        have hnextComp := B.firstGap_rightConnector_isCompOf j e heq 0 (by
          exact hrightPos) (by
            simpa [cycle, auxiliaryCycleWord, OsinComponents.length_revWord] using hn)
        have hnextEq : P.label s = P.label
            (HalfEntry.entrySource B.brokenAssignment.index.first e) :=
          eq_of_isCompOf_of_isCompOf hletter hnextComp
        have hparent := B.firstArc_targetComponent hsData.1
        have hnextLetter : (B.firstArc[B.firstArcCut
            (B.firstTargetSide (HalfEntry.entrySource
              B.brokenAssignment.index.first e))]'(by
                exact B.firstArc_isCutPath.cut.le_length
                  (B.firstTargetSide_lt heTarget).le)).IsCompOf (P.label s) := by
          have hh := hparent.2.2.1 _ le_rfl (by omega) _
          simpa only [hnextEq] using hh
        exact hlocalComp.2.2.2.2 _ (by omega) (by omega) hnextLetter
  have hraw := firstGapArcSource_cycleComponent_of_boundary B j s hstart hend
-/

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
