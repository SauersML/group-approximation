import GroupApproximation.Dynamics.RankTwoCoreImageHaagerup
import GroupApproximation.Dynamics.ClopenCrossedProductAlgebra
import GroupApproximation.Dynamics.TransientCellsClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-two limitation of the compression method, closed

`non_mf_groups_exist.tex`, `sec:chain-core`, the remark after `cor:dynamic-rank-budget`
(tex 1794–1807):

> There is also a limitation of the compression method at rank two.  If the core $Y$ consists of
> fixed points, every Kazhdan subgroup of $\GL_2(R_X)$ is finite.  Its finitely generated
> restriction image lies in a finite product of groups $\GL_2(k[z,z^{-1}])$, hence in a Haagerup
> group by~\cite[Theorem~4]{GHW}, and is finite.  The remaining kernel is locally finite, so a
> finite-index subgroup of the Kazhdan group is finitely generated and locally finite, hence
> finite.  Finite subgroups have no proper self-compressions, so their compression defects are
> trivial.  The same reasoning applies to unit groups when every core point has period at most
> two: a finite invariant clopen partition gives matrix blocks of size at most two over
> $k[z,z^{-1}]$.

The remaining kernel is locally finite because the transient ideal is locally matricial over the
finite field (`lem:transient-matrices`, `ClopenCrossedProduct.transientIdealLocallyMatricialStatement_holds`),
through `coreRestrictionLocallyFiniteKernel_of_transientLocallyMatricial`.  With the closed image steps
(`RankTwoCoreImageHaagerup`) every printed endpoint of the remark is closed:

* `coreRestrictionLocallyFiniteKernel : CoreRestrictionLocallyFiniteKernelStatement`;
* `printedFixedCoreGLTwoKazhdanFinite : PrintedFixedCoreGLTwoKazhdanFinite` (tex 1795–1800);
* `printedPeriodTwoCoreUnitsKazhdanFinite : PrintedPeriodTwoCoreUnitsKazhdanFinite` (tex 1802–1805);
* `printedRankTwoCompressionDefectsTrivial : PrintedRankTwoCompressionDefectsTrivial` (tex 1801–1802).
-/

namespace GroupApproximation
namespace ChainCore
namespace RankTwoLimit

/-- **The remaining kernel (tex 1799)**, closed: over a finite field, the kernel of core restriction
`R_X → R_Y` is locally finite. -/
theorem coreRestrictionLocallyFiniteKernel : CoreRestrictionLocallyFiniteKernelStatement :=
  coreRestrictionLocallyFiniteKernel_of_transientLocallyMatricial
    ClopenCrossedProduct.transientIdealLocallyMatricialStatement_holds

/-- **Printed (tex 1795–1800)**, closed.  "If the core $Y$ consists of fixed points, every Kazhdan
subgroup of $\GL_2(R_X)$ is finite." -/
theorem printedFixedCoreGLTwoKazhdanFinite : PrintedFixedCoreGLTwoKazhdanFinite :=
  printedFixedCoreGLTwoKazhdanFinite_of_kernel coreRestrictionLocallyFiniteKernel

/-- **Printed (tex 1802–1805)**, closed.  "The same reasoning applies to unit groups when every core
point has period at most two." -/
theorem printedPeriodTwoCoreUnitsKazhdanFinite : PrintedPeriodTwoCoreUnitsKazhdanFinite :=
  printedPeriodTwoCoreUnitsKazhdanFinite_of_kernel coreRestrictionLocallyFiniteKernel

/-- **Printed (tex 1801–1802)**, closed.  "Finite subgroups have no proper self-compressions, so
their compression defects are trivial", in both rank-two cases. -/
theorem printedRankTwoCompressionDefectsTrivial : PrintedRankTwoCompressionDefectsTrivial :=
  printedRankTwoCompressionDefectsTrivial_of_kernel coreRestrictionLocallyFiniteKernel

end RankTwoLimit
end ChainCore
end GroupApproximation

#audit_closed_axioms GroupApproximation.ChainCore.RankTwoLimit.coreRestrictionLocallyFiniteKernel
#audit_closed_axioms GroupApproximation.ChainCore.RankTwoLimit.printedFixedCoreGLTwoKazhdanFinite
#audit_closed_axioms GroupApproximation.ChainCore.RankTwoLimit.printedPeriodTwoCoreUnitsKazhdanFinite
#audit_closed_axioms GroupApproximation.ChainCore.RankTwoLimit.printedRankTwoCompressionDefectsTrivial
