import GroupApproximation.GGT.DGOProposition414GapChildTargetComponents
import GroupApproximation.GGT.DGOProposition414GapComponentAssembly

/-!
# Connector target components in balanced gap children

The connector sides in a DGO auxiliary cycle have length at most one.  This
module transfers the literal connector letters to their exact full-cycle
singleton components.  The predecessor and successor exclusions are the two
maximality clauses at a connector endpoint; all cut coordinates are reduced by
the canonical auxiliary-cycle cut equations.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- The nonempty first-gap left connector is a full-cycle component at index
zero when its successor letter has a different label. -/
theorem firstGap_leftConnector_cycleComponent
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (hprev : HalfGap.previousEntry B.brokenAssignment.index.first j = some e)
    (hzero : 0 < (B.firstGapLeft j).length)
    (hnext : ∀ hn : 1 < (B.firstGapCycle j).length,
      ¬ ((B.firstGapCycle j)[1]'hn).IsCompOf (B.firstGapLocalLabel j 0)) :
    IsComp (B.firstGapLocalLabel j 0) (B.firstGapCycle j)
      (B.firstGapCut j 0) (B.firstGapCut j 1) := by
  have hcycle : 0 < (B.firstGapCycle j).length := by
    simp only [firstGapCycle, auxiliaryCycleWord, List.length_append,
      OsinComponents.length_revWord]
    omega
  have hletter := B.firstGap_leftConnector_isCompOf j e hprev 0 hzero hcycle
  have hcomp := isComp_singleton_of_boundary
    (B.firstGapLocalLabel j 0) (B.firstGapCycle j) hcycle hletter
    (by intro q hq; omega) hnext
  have hcut0 : auxiliaryCycleCut (B.firstGapLeft j)
      (B.firstGapFinishSide j - B.firstGapStartSide j)
      (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j)) (B.firstGapRight j) 0 = 0 :=
    auxiliaryCycleCut_left (B.firstGapLeft j) (B.firstGapRight j)
      (B.firstGapFinishSide j - B.firstGapStartSide j)
      (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j)) (r := 0) (by omega)
  have hcut1 : auxiliaryCycleCut (B.firstGapLeft j)
      (B.firstGapFinishSide j - B.firstGapStartSide j)
      (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j)) (B.firstGapRight j) 1 = 1 :=
    auxiliaryCycleCut_left (B.firstGapLeft j) (B.firstGapRight j)
      (B.firstGapFinishSide j - B.firstGapStartSide j)
      (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j)) (r := 1) (by omega)
  simpa only [firstGapCut, hcut0, hcut1] using hcomp

/-- The first-gap right connector is a full-cycle singleton at the end of the
arc block when its predecessor and successor letters have different labels. -/
theorem firstGap_rightConnector_cycleComponent
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (hnextEntry : HalfGap.nextEntry B.brokenAssignment.index.first j = some e)
    (hzero : 0 < (B.firstGapRight j).length)
    (hprev : ∀ q : ℕ,
      (B.firstGapLeft j).length +
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)).length = q + 1 →
      ∀ hq : q < (B.firstGapCycle j).length,
      ¬ ((B.firstGapCycle j)[q]'hq).IsCompOf
        (B.firstGapLocalLabel j ((B.firstGapLeft j).length +
          (B.firstGapFinishSide j - B.firstGapStartSide j))))
    (hnext : ∀ hn : (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length + 1 <
        (B.firstGapCycle j).length,
      ¬ ((B.firstGapCycle j).get ⟨
        (B.firstGapLeft j).length +
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)).length + 1, hn⟩).IsCompOf
        (B.firstGapLocalLabel j ((B.firstGapLeft j).length +
          (B.firstGapFinishSide j - B.firstGapStartSide j)))) :
    IsComp (B.firstGapLocalLabel j ((B.firstGapLeft j).length +
        (B.firstGapFinishSide j - B.firstGapStartSide j)))
      (B.firstGapCycle j)
      (B.firstGapCut j ((B.firstGapLeft j).length +
        (B.firstGapFinishSide j - B.firstGapStartSide j)))
      (B.firstGapCut j ((B.firstGapLeft j).length +
        (B.firstGapFinishSide j - B.firstGapStartSide j) + 1)) := by
  have hcycle : (B.firstGapLeft j).length +
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)).length <
      (B.firstGapCycle j).length := by
    simp only [firstGapCycle, auxiliaryCycleWord, List.length_append,
      OsinComponents.length_revWord]
    omega
  have hletter := B.firstGap_rightConnector_isCompOf j e hnextEntry 0 hzero
    (by omega : (B.firstGapLeft j).length +
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)).length <
      (B.firstGapCycle j).length)
  have hcomp := isComp_singleton_of_boundary
    (B.firstGapLocalLabel j ((B.firstGapLeft j).length +
      (B.firstGapFinishSide j - B.firstGapStartSide j)))
    (B.firstGapCycle j) hcycle hletter hprev hnext
  have harc : IsPolygonCut
      (B.firstGapFinishSide j - B.firstGapStartSide j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j))
      (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j)) :=
    isPolygonCut_arcWord B.firstArc_isCutPath.cut
      (B.firstGap_side_order j) (B.firstGapFinishSide_le j)
  have hcut0 : auxiliaryCycleCut (B.firstGapLeft j)
      (B.firstGapFinishSide j - B.firstGapStartSide j)
      (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j)) (B.firstGapRight j)
      ((B.firstGapLeft j).length +
        (B.firstGapFinishSide j - B.firstGapStartSide j)) =
      (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length := by
    have hraw := auxiliaryCycleCut_right (B.firstGapLeft j) (B.firstGapRight j)
      (arc := arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j))
      (nArc := B.firstGapFinishSide j - B.firstGapStartSide j)
      (arcCut := fun r => B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j))
      (harc) (r := 0) (by omega)
    simpa only [Nat.add_zero] using hraw
  have hcut1 : auxiliaryCycleCut (B.firstGapLeft j)
      (B.firstGapFinishSide j - B.firstGapStartSide j)
      (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j)) (B.firstGapRight j)
      ((B.firstGapLeft j).length +
        (B.firstGapFinishSide j - B.firstGapStartSide j) + 1) =
      (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length + 1 := by
    rw [auxiliaryCycleCut_right (B.firstGapLeft j) (B.firstGapRight j)
      (arc := arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j))
      (nArc := B.firstGapFinishSide j - B.firstGapStartSide j)
      (arcCut := fun r => B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j))
      (harc) (r := 1) (by omega)]
  simpa only [firstGapCut, hcut0, hcut1] using hcomp

/-- The wrapped-half left connector is a full-cycle singleton at index zero
under the analogous successor exclusion. -/
theorem secondGap_leftConnector_cycleComponent
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (hprev : HalfGap.previousEntry B.brokenAssignment.index.second j = some e)
    (hzero : 0 < (B.secondGapLeft j).length)
    (hnext : ∀ hn : 1 < (B.secondGapCycle j).length,
      ¬ ((B.secondGapCycle j)[1]'hn).IsCompOf (B.secondGapLocalLabel j 0)) :
    IsComp (B.secondGapLocalLabel j 0) (B.secondGapCycle j)
      (B.secondGapCut j 0) (B.secondGapCut j 1) := by
  have hcycle : 0 < (B.secondGapCycle j).length := by
    simp only [secondGapCycle, auxiliaryCycleWord, List.length_append,
      OsinComponents.length_revWord]
    omega
  have hletter := B.secondGap_leftConnector_isCompOf j e hprev 0 hzero hcycle
  have hcomp := isComp_singleton_of_boundary
    (B.secondGapLocalLabel j 0) (B.secondGapCycle j) hcycle hletter
    (by intro q hq; omega) hnext
  have hcut0 : auxiliaryCycleCut (B.secondGapLeft j)
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j)) (B.secondGapRight j) 0 = 0 :=
    auxiliaryCycleCut_left (B.secondGapLeft j) (B.secondGapRight j)
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j)) (r := 0) (by omega)
  have hcut1 : auxiliaryCycleCut (B.secondGapLeft j)
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j)) (B.secondGapRight j) 1 = 1 :=
    auxiliaryCycleCut_left (B.secondGapLeft j) (B.secondGapRight j)
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j)) (r := 1) (by omega)
  simpa only [secondGapCut, hcut0, hcut1] using hcomp

/-- The wrapped-half right connector is a full-cycle singleton at the end of
the arc block under the two boundary exclusions. -/
theorem secondGap_rightConnector_cycleComponent
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (hnextEntry : HalfGap.nextEntry B.brokenAssignment.index.second j = some e)
    (hzero : 0 < (B.secondGapRight j).length)
    (hprev : ∀ q : ℕ,
      (B.secondGapLeft j).length +
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)).length = q + 1 →
      ∀ hq : q < (B.secondGapCycle j).length,
      ¬ ((B.secondGapCycle j)[q]'hq).IsCompOf
        (B.secondGapLocalLabel j ((B.secondGapLeft j).length +
          (B.secondGapFinishSide j - B.secondGapStartSide j))))
    (hnext : ∀ hn : (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length + 1 <
        (B.secondGapCycle j).length,
      ¬ ((B.secondGapCycle j).get ⟨
        (B.secondGapLeft j).length +
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)).length + 1, hn⟩).IsCompOf
        (B.secondGapLocalLabel j ((B.secondGapLeft j).length +
          (B.secondGapFinishSide j - B.secondGapStartSide j)))) :
    IsComp (B.secondGapLocalLabel j ((B.secondGapLeft j).length +
        (B.secondGapFinishSide j - B.secondGapStartSide j)))
      (B.secondGapCycle j)
      (B.secondGapCut j ((B.secondGapLeft j).length +
        (B.secondGapFinishSide j - B.secondGapStartSide j)))
      (B.secondGapCut j ((B.secondGapLeft j).length +
        (B.secondGapFinishSide j - B.secondGapStartSide j) + 1)) := by
  have hcycle : (B.secondGapLeft j).length +
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)).length <
      (B.secondGapCycle j).length := by
    simp only [secondGapCycle, auxiliaryCycleWord, List.length_append,
      OsinComponents.length_revWord]
    omega
  have hletter := B.secondGap_rightConnector_isCompOf j e hnextEntry 0 hzero
    (by omega : (B.secondGapLeft j).length +
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)).length <
      (B.secondGapCycle j).length)
  have hcomp := isComp_singleton_of_boundary
    (B.secondGapLocalLabel j ((B.secondGapLeft j).length +
      (B.secondGapFinishSide j - B.secondGapStartSide j)))
    (B.secondGapCycle j) hcycle hletter hprev hnext
  have harc : IsPolygonCut
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j))
      (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j)) :=
    isPolygonCut_arcWord B.secondArc_isCutPath.cut
      (B.secondGap_side_order j) (B.secondGapFinishSide_le j)
  have hcut0 : auxiliaryCycleCut (B.secondGapLeft j)
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j)) (B.secondGapRight j)
      ((B.secondGapLeft j).length +
        (B.secondGapFinishSide j - B.secondGapStartSide j)) =
      (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length := by
    have hraw := auxiliaryCycleCut_right (B.secondGapLeft j) (B.secondGapRight j)
      (arc := arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j))
      (nArc := B.secondGapFinishSide j - B.secondGapStartSide j)
      (arcCut := fun r => B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j))
      (harc) (r := 0) (by omega)
    simpa only [Nat.add_zero] using hraw
  have hcut1 : auxiliaryCycleCut (B.secondGapLeft j)
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j)) (B.secondGapRight j)
      ((B.secondGapLeft j).length +
        (B.secondGapFinishSide j - B.secondGapStartSide j) + 1) =
      (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length + 1 := by
    rw [auxiliaryCycleCut_right (B.secondGapLeft j) (B.secondGapRight j)
      (arc := arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j))
      (nArc := B.secondGapFinishSide j - B.secondGapStartSide j)
      (arcCut := fun r => B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j))
      (harc) (r := 1) (by omega)]
  simpa only [secondGapCut, hcut0, hcut1] using hcomp

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
