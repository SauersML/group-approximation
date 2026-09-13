import GroupApproximation.Algebra.LocallyFiniteCongruenceKernel
import GroupApproximation.Dynamics.ClopenCrossedProductComap
import GroupApproximation.Dynamics.ChainRecurrence
import GroupApproximation.Kazhdan.HaagerupKazhdanFinite
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefect
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-two limitation of the compression method: statements

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
> $k[z,z^{-1}]$.  Thus the threshold three is a limit of this method in these cases, not a proof
> that the unrestricted $\GL_2$ or $\EL_3$ conclusions are false.

This module states each step as a named proposition, so the assembly and the producers can land
independently.  `X` carries a compatible metric (the printed definition of `CR(T)` uses one), `k`
is a finite field, `R_X = ClopenCrossedProduct T k`, `Y = chainRecurrentSet T`, and restriction is
`ClopenCrossedProduct.restrict T k (image_chainRecurrentSet T)`.

* Steps: `FixedCoreImageHaagerupStatement`, `PeriodTwoCoreUnitImageHaagerupStatement` (the restriction
  images), `CoreRestrictionLocallyFiniteKernelStatement` (the remaining kernel, from
  `lem:transient-matrices`);
* printed endpoints: `PrintedFixedCoreGLTwoKazhdanFinite`, `PrintedPeriodTwoCoreUnitsKazhdanFinite`,
  `PrintedRankTwoCompressionDefectsTrivial`.
-/

namespace GroupApproximation
namespace ChainCore
namespace RankTwoLimit

open Haagerup Dynamics Manuscript.OneSidedMFRadical

/-- **Step (tex 1796–1798), fixed core.**  Over a finite field, when the homeomorphism of the core
is the identity, every countable subgroup of `GL_2(R_Y)` has the Haagerup property: a finitely
generated one lies in a finite product of groups `GL_2(k[z,z^{-1}])`. -/
def FixedCoreImageHaagerupStatement : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] (S : Y ≃ₜ Y) (k : Type) [Field k] [Finite k],
    (∀ y, S y = y) → ∀ M : Subgroup (GL (Fin 2) (ClopenCrossedProduct S k)), Countable M →
      HasHaagerupProperty.{0, 0} M

/-- **Step (tex 1802–1805), core periods at most two.**  Over a finite field, when every point of the
core has period at most two, every countable subgroup of `R_Y^×` has the Haagerup property: a finite
invariant clopen partition gives matrix blocks of size at most two over `k[z,z^{-1}]`. -/
def PeriodTwoCoreUnitImageHaagerupStatement : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] (S : Y ≃ₜ Y) (k : Type) [Field k] [Finite k],
    (∀ y, S (S y) = y) → ∀ M : Subgroup (ClopenCrossedProduct S k)ˣ, Countable M →
      HasHaagerupProperty.{0, 0} M

/-- **Step (tex 1799), the remaining kernel.**  Over a finite field, every finite subset of the
kernel of core restriction `R_X → R_Y` lies in a finite subring of that kernel (the transient ideal
is locally matricial, `lem:transient-matrices`). -/
def CoreRestrictionLocallyFiniteKernelStatement : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (k : Type) [Field k] [Finite k],
    HasLocallyFiniteKernel (ClopenCrossedProduct.restrict T k (image_chainRecurrentSet T))

/-- **Printed (tex 1795–1796).**  "If the core $Y$ consists of fixed points, every Kazhdan subgroup
of $\GL_2(R_X)$ is finite." -/
def PrintedFixedCoreGLTwoKazhdanFinite : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (k : Type) [Field k] [Finite k], (∀ y ∈ chainRecurrentSet T, T y = y) →
      ∀ H : Subgroup (GL (Fin 2) (ClopenCrossedProduct T k)), HasKazhdanPropertyT.{0, 0} H →
        Finite H

/-- **Printed (tex 1802–1803).**  "The same reasoning applies to unit groups when every core point
has period at most two": every Kazhdan subgroup of `R_X^×` is finite. -/
def PrintedPeriodTwoCoreUnitsKazhdanFinite : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (k : Type) [Field k] [Finite k], (∀ y ∈ chainRecurrentSet T, T (T y) = y) →
      ∀ H : Subgroup (ClopenCrossedProduct T k)ˣ, HasKazhdanPropertyT.{0, 0} H → Finite H

/-- **Printed (tex 1801–1802).**  "Finite subgroups have no proper self-compressions, so their
compression defects are trivial."  In both cases every Kazhdan subgroup `L` has `𝔇_G(L) = 1`. -/
def PrintedRankTwoCompressionDefectsTrivial : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (k : Type) [Field k] [Finite k],
    ((∀ y ∈ chainRecurrentSet T, T y = y) →
      ∀ L : Subgroup (GL (Fin 2) (ClopenCrossedProduct T k)), HasKazhdanPropertyT.{0, 0} L →
        printedDefect L = ⊥) ∧
    ((∀ y ∈ chainRecurrentSet T, T (T y) = y) →
      ∀ L : Subgroup (ClopenCrossedProduct T k)ˣ, HasKazhdanPropertyT.{0, 0} L →
        printedDefect L = ⊥)

end RankTwoLimit
end ChainCore
end GroupApproximation

#audit_axioms GroupApproximation.ChainCore.RankTwoLimit.FixedCoreImageHaagerupStatement
#audit_axioms GroupApproximation.ChainCore.RankTwoLimit.PeriodTwoCoreUnitImageHaagerupStatement
#audit_axioms GroupApproximation.ChainCore.RankTwoLimit.CoreRestrictionLocallyFiniteKernelStatement
#audit_axioms GroupApproximation.ChainCore.RankTwoLimit.PrintedFixedCoreGLTwoKazhdanFinite
#audit_axioms GroupApproximation.ChainCore.RankTwoLimit.PrintedPeriodTwoCoreUnitsKazhdanFinite
#audit_axioms GroupApproximation.ChainCore.RankTwoLimit.PrintedRankTwoCompressionDefectsTrivial
