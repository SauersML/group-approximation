import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.BinderFiveCopyRegion
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalkOrder
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellCopyClean
import GroupApproximation.Meta.AxiomGuard

/-!
# Binder 5 below the bound, from the refuted walk binder

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

`multipleEdgePocketRegionCopyBelowInput_of_pinchBelowSectionOrderEuler` and
`osinMultipleEdgePocketRegionCopyBelowSection_of_pinchBelowSectionOrderEuler`
(`Common/CellStepBelow.lean`) build binder 5 below the bound from the clean copy in both orders, the
exterior off one side, the Euler residual, the below pinch (residual 06) and the below proper arcs
(residual 07).  With the refuted walk binder (`CellPocketWalkRefutedBelowInput`,
`RefutedDef.lean`), binder 5 needs only the clean copy and the exterior off one side, and both are
closed in the corpus (`cellPocketCopyCleanBothOrders`, `cellPocketWalkOuterOffSideSomeOrder`).

* `multipleEdgePocketRegionCopyBelowInput_of_refuted`: binder 5 below the bound at fixed parameters,
  from the two order residuals and the refuted binder.
* `osinMultipleEdgePocketRegionCopyBelowSection_of_refuted`: binder 5 below the bound beyond
  thresholds, from the refuted section binder alone, at its thresholds (no `max`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

section Order

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **Binder 5 on a copy below the inductive bound, from the refuted walk binder**, at fixed
parameters.  As `multipleEdgePocketRegionCopyBelowInput_of_pinchBelowSectionOrderEuler`: pass to
the clean copy in both orders, take the walks of both orders, and use the walk with the exterior off
its side. -/
theorem multipleEdgePocketRegionCopyBelowInput_of_refuted
    (hcopy : CellPocketCopyCleanBothOrdersStatement.{u, w, v})
    (hout : CellPocketWalkOuterOffSideSomeOrderStatement.{u, w, v})
    {D : RelGenSet G Lambda} {lambda c mu : ℝ} {eps : ℕ}
    (hrefuted : CellPocketWalkRefutedBelowInput.{u, w, v} D lambda c mu eps W) :
    MultipleEdgePocketRegionCopyBelowInput.{u, w, v} D lambda c mu eps W := by
  intro Delta cuts hlea hbelow S a ha b hb hab i j hij hai hbi
  obtain ⟨S', a', b', i', j', ha', hb', hab', hij', hai', hbi', hclean₁, hclean₂⟩ :=
    hcopy D lambda c eps W Delta cuts hlea S a ha b hb hab i j hij hai hbi
  have hlea' : S'.diagram.LeastArea := S'.equiv.leastArea hlea
  obtain ⟨K₁, hf₁, hs₁, hA₁, hB₁, hne₁, hch₁, hcl₁⟩ :=
    CellPocketWalk.exists_of_joinsCells_closedWalk S'.toRealizedSectionFamily ha' hb' hab' hij'
      hai' hbi'
  obtain ⟨hnd₁, hal₁⟩ := K₁.walk_nodup_and_alpha_not_mem hlea' hij' hf₁ hs₁
    (S'.pairwise a' ha' b' hb' hab') hclean₁
  obtain ⟨K₂, hf₂, hs₂, hA₂, hB₂, hne₂, hch₂, hcl₂⟩ :=
    CellPocketWalk.exists_of_joinsCells_closedWalk S'.toRealizedSectionFamily hb' ha' hab'.symm
      hij' hbi' hai'
  obtain ⟨hnd₂, hal₂⟩ := K₂.walk_nodup_and_alpha_not_mem hlea' hij' hf₂ hs₂
    (S'.pairwise b' hb' a' ha' hab'.symm) hclean₂
  rcases hout S'.toRealizedSectionFamily ha' hb' hab' hij' hai' hbi' K₁ K₂ hf₁ hs₁ hA₁ hB₁ hne₁
      hch₁ hcl₁ hnd₁ hal₁ hf₂ hs₂ hA₂ hB₂ hne₂ hch₂ hcl₂ hnd₂ hal₂ with hoff | hoff
  · exact copyRegion_of_offSideWalkSectionRefutedBelow hrefuted hlea hbelow S' ha' hb' hab' hij'
      hai' hbi' hclean₁ K₁ hf₁ hs₁ hA₁ hB₁ hne₁ hch₁ hcl₁ hnd₁ hal₁ hoff
  · exact copyRegion_of_offSideWalkSectionRefutedBelow hrefuted hlea hbelow S' hb' ha' hab'.symm
      hij' hbi' hai' hclean₂ K₂ hf₂ hs₂ hA₂ hB₂ hne₂ hch₂ hcl₂ hnd₂ hal₂ hoff

end Order

/-- **Binder 5 on a copy below the inductive bound, beyond thresholds, from the refuted section
binder.**  The thresholds are those of the refuted binder; the clean copy in both orders and the
exterior off one side are the closed corpus theorems.  No Euler residual and no pinch. -/
theorem osinMultipleEdgePocketRegionCopyBelowSection_of_refuted
    (hrefuted : CellPocketWalkRefutedBelowSectionStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := hrefuted D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hW =>
    multipleEdgePocketRegionCopyBelowInput_of_refuted cellPocketCopyCleanBothOrders
      cellPocketWalkOuterOffSideSomeOrder (hrho rho hrho' W hW)⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.multipleEdgePocketRegionCopyBelowInput_of_refuted
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted
