import GroupApproximation.GGT.DGOProposition414GapArcPartition
import GroupApproximation.GGT.DGOProposition414GapSurvivors

/-!
# Gap owners of surviving balanced components

A distinguished side which survives a balanced half cut is absent from that
half's ordered list of broken sides.  The ordered-gap covering lemma then
places it in a unique canonical gap.  This is the surviving-side part of the
factor placement in Dahmani--Guirardel--Osin Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- A surviving first-half target side is not one of the ordered broken
sides. -/
theorem firstTargetSide_not_mem_firstBrokenSides_of_survives
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.componentPlacement.firstTarget)
    (hsurvives : B.componentPlacement.firstSurvives s) :
    B.firstTargetSide s ∉ B.firstBrokenSides := by
  intro hmem
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
  let e : Fin B.brokenAssignment.index.first.sources.length := by
    refine ⟨i, ?_⟩
    simpa [firstBrokenSides] using hi
  let t := HalfEntry.entrySource B.brokenAssignment.index.first e
  have htBroken := HalfEntry.entrySource_mem
    B.brokenAssignment.index.first e
  have htTarget := (mem_brokenSet_iff.mp htBroken).1
  have hside : B.firstTargetSide s = B.firstTargetSide t := by
    simpa [firstBrokenSides, e, t] using heq
  have hpos : B.componentPlacement.firstPos s =
      B.componentPlacement.firstPos t := by
    have hcutS := (B.firstArcCut_target hs).1
    have hcutT := (B.firstArcCut_target htTarget).1
    change B.firstTargetPos s = B.firstTargetPos t
    rw [← hcutS, ← hcutT, hside]
  have hst : s = t :=
    B.componentPlacement.firstPos_injective hs htTarget hpos
  subst t
  exact (mem_brokenSet_iff.mp htBroken).2 hsurvives

/-- A surviving wrapped-half target side is not one of the ordered broken
sides. -/
theorem secondTargetSide_not_mem_secondBrokenSides_of_survives
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.componentPlacement.secondTarget)
    (hsurvives : B.componentPlacement.secondSurvives s) :
    B.secondTargetSide s ∉ B.secondBrokenSides := by
  intro hmem
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
  let e : Fin B.brokenAssignment.index.second.sources.length := by
    refine ⟨i, ?_⟩
    simpa [secondBrokenSides] using hi
  let t := HalfEntry.entrySource B.brokenAssignment.index.second e
  have htBroken := HalfEntry.entrySource_mem
    B.brokenAssignment.index.second e
  have htTarget := (mem_brokenSet_iff.mp htBroken).1
  have hside : B.secondTargetSide s = B.secondTargetSide t := by
    simpa [secondBrokenSides, e, t] using heq
  have hpos : B.componentPlacement.secondPos s =
      B.componentPlacement.secondPos t := by
    have hcutS := (B.secondArcCut_target hs).1
    have hcutT := (B.secondArcCut_target htTarget).1
    change B.secondTargetPos s = B.secondTargetPos t
    rw [← hcutS, ← hcutT, hside]
  have hst : s = t :=
    B.componentPlacement.secondPos_injective hs htTarget hpos
  subst t
  exact (mem_brokenSet_iff.mp htBroken).2 hsurvives

/-- Canonical gap containing a surviving first-half target. -/
noncomputable def firstSurvivorGapOwner
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.componentPlacement.firstTarget)
    (hsurvives : B.componentPlacement.firstSurvives s) :
    Fin B.brokenAssignment.index.first.pieceCount :=
  Classical.choose (exists_orderedGap_of_not_mem 0
    (B.secondSide - B.firstSide + 1) (B.firstTargetSide s)
    B.firstBrokenSides (Nat.zero_le _) (B.firstTargetSide_lt hs)
    (B.firstTargetSide_not_mem_firstBrokenSides_of_survives hs hsurvives)
    B.firstBrokenSides_pairwise)

/-- The surviving first-half source belongs to its canonical gap's inherited
target set. -/
theorem firstSurvivorGapOwner_mem
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.componentPlacement.firstTarget)
    (hsurvives : B.componentPlacement.firstSurvives s) :
    s ∈ B.firstGapArcSources (B.firstSurvivorGapOwner hs hsurvives) := by
  classical
  have hgap := Classical.choose_spec (exists_orderedGap_of_not_mem 0
    (B.secondSide - B.firstSide + 1) (B.firstTargetSide s)
    B.firstBrokenSides (Nat.zero_le _) (B.firstTargetSide_lt hs)
    (B.firstTargetSide_not_mem_firstBrokenSides_of_survives hs hsurvives)
    B.firstBrokenSides_pairwise)
  rw [← B.firstGapStartSide_eq_orderedGapStart,
    ← B.firstGapFinishSide_eq_orderedGapFinish] at hgap
  exact Finset.mem_filter.mpr ⟨hs, hgap⟩

/-- Canonical gap containing a surviving wrapped-half target. -/
noncomputable def secondSurvivorGapOwner
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.componentPlacement.secondTarget)
    (hsurvives : B.componentPlacement.secondSurvives s) :
    Fin B.brokenAssignment.index.second.pieceCount :=
  Classical.choose (exists_orderedGap_of_not_mem 0
    ((n - B.secondSide) + B.firstSide + 1) (B.secondTargetSide s)
    B.secondBrokenSides (Nat.zero_le _) (B.secondTargetSide_lt hs)
    (B.secondTargetSide_not_mem_secondBrokenSides_of_survives hs hsurvives)
    B.secondBrokenSides_pairwise)

/-- The surviving wrapped-half source belongs to its canonical gap's
inherited target set. -/
theorem secondSurvivorGapOwner_mem
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.componentPlacement.secondTarget)
    (hsurvives : B.componentPlacement.secondSurvives s) :
    s ∈ B.secondGapArcSources (B.secondSurvivorGapOwner hs hsurvives) := by
  classical
  have hgap := Classical.choose_spec (exists_orderedGap_of_not_mem 0
    ((n - B.secondSide) + B.firstSide + 1) (B.secondTargetSide s)
    B.secondBrokenSides (Nat.zero_le _) (B.secondTargetSide_lt hs)
    (B.secondTargetSide_not_mem_secondBrokenSides_of_survives hs hsurvives)
    B.secondBrokenSides_pairwise)
  rw [← B.secondGapStartSide_eq_orderedGapStart,
    ← B.secondGapFinishSide_eq_orderedGapFinish] at hgap
  exact Finset.mem_filter.mpr ⟨hs, hgap⟩

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
