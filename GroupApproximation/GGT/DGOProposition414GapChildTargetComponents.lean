import GroupApproximation.GGT.DGOProposition414GapChordComponents
import GroupApproximation.GGT.DGOProposition414GapConnectorComponents

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

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
