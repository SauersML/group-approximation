import GroupApproximation.Dynamics.RankTwoKazhdanLimitStatements
import GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonRankTwoInert
import GroupApproximation.Manuscript.OneSidedMFRadical.DefectSaturation
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-two limitation of the compression method: assembly

`non_mf_groups_exist.tex`, `sec:chain-core`, the remark after `cor:dynamic-rank-budget`
(tex 1794–1807).  The printed deduction, over the step propositions of
`RankTwoKazhdanLimitStatements`:

* a Kazhdan subgroup `H ≤ GL_2(R_X)` (resp. `≤ R_X^×`) has a Kazhdan restriction image in
  `GL_2(R_Y)` (resp. `R_Y^×`); the image is finitely generated and has the Haagerup property, hence is
  finite; the kernel of `H → image` has finite index and is locally finite, so `H` is finite
  (`JacobsonRankTwo.finite_image_and_finite_of_kazhdan`, closed on main);
* the remaining kernel is locally finite (`isLocallyFiniteGroup_ker_glMap`,
  `isLocallyFiniteGroup_ker_unitsMap`) once core restriction has a locally finite kernel;
* finite subgroups have trivial printed defect (`printedDefect_eq_bot_of_finite`).
-/

namespace GroupApproximation
namespace ChainCore
namespace RankTwoLimit

open Haagerup Dynamics Manuscript.OneSidedMFRadical

/-- **Assembly (tex 1795–1800), fixed core.** -/
theorem printedFixedCoreGLTwoKazhdanFinite_of_steps
    (hker : CoreRestrictionLocallyFiniteKernelStatement)
    (himg : FixedCoreImageHaagerupStatement) : PrintedFixedCoreGLTwoKazhdanFinite := by
  intro X _ _ _ T k _ _ hfix H hH
  have hY := image_chainRecurrentSet T
  have hS : ∀ y, ClopenCrossedProduct.restrictHomeo T hY y = y := fun y ↦
    Subtype.ext (hfix y y.2)
  exact (JacobsonRankTwo.finite_image_and_finite_of_kazhdan
    (glMap (Fin 2) (ClopenCrossedProduct.restrict T k hY))
    (isLocallyFiniteGroup_ker_glMap _ (hker X T k))
    (himg _ (ClopenCrossedProduct.restrictHomeo T hY) k hS) H hH).2.2.2

/-- **Assembly (tex 1802–1805), core periods at most two.** -/
theorem printedPeriodTwoCoreUnitsKazhdanFinite_of_steps
    (hker : CoreRestrictionLocallyFiniteKernelStatement)
    (himg : PeriodTwoCoreUnitImageHaagerupStatement) : PrintedPeriodTwoCoreUnitsKazhdanFinite := by
  intro X _ _ _ T k _ _ hper H hH
  have hY := image_chainRecurrentSet T
  have hS : ∀ y, ClopenCrossedProduct.restrictHomeo T hY
      (ClopenCrossedProduct.restrictHomeo T hY y) = y := fun y ↦
    Subtype.ext (hper y y.2)
  exact (JacobsonRankTwo.finite_image_and_finite_of_kazhdan
    (Units.map (ClopenCrossedProduct.restrict T k hY : ClopenCrossedProduct T k →*
      ClopenCrossedProduct (ClopenCrossedProduct.restrictHomeo T hY) k))
    (isLocallyFiniteGroup_ker_unitsMap _ (hker X T k))
    (himg _ (ClopenCrossedProduct.restrictHomeo T hY) k hS) H hH).2.2.2

/-- **Assembly (tex 1801–1802).**  Kazhdan subgroups in both cases are finite, so their printed
compression defects are trivial. -/
theorem printedRankTwoCompressionDefectsTrivial_of_steps
    (hker : CoreRestrictionLocallyFiniteKernelStatement)
    (himg : FixedCoreImageHaagerupStatement) (himg2 : PeriodTwoCoreUnitImageHaagerupStatement) :
    PrintedRankTwoCompressionDefectsTrivial := by
  intro X _ _ _ T k _ _
  refine ⟨fun hfix L hL ↦ ?_, fun hper L hL ↦ ?_⟩
  · haveI : Finite L :=
      printedFixedCoreGLTwoKazhdanFinite_of_steps hker himg X T k hfix L hL
    exact printedDefect_eq_bot_of_finite L
  · haveI : Finite L :=
      printedPeriodTwoCoreUnitsKazhdanFinite_of_steps hker himg2 X T k hper L hL
    exact printedDefect_eq_bot_of_finite L

end RankTwoLimit
end ChainCore
end GroupApproximation

#audit_axioms GroupApproximation.ChainCore.RankTwoLimit.printedFixedCoreGLTwoKazhdanFinite_of_steps
#audit_axioms GroupApproximation.ChainCore.RankTwoLimit.printedPeriodTwoCoreUnitsKazhdanFinite_of_steps
#audit_axioms GroupApproximation.ChainCore.RankTwoLimit.printedRankTwoCompressionDefectsTrivial_of_steps
