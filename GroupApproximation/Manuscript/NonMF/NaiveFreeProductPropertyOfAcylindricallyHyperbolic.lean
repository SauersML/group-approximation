import GroupApproximation.Manuscript.NonMF.NaiveFreeProductAtAcylindricallyHyperbolicProof
import GroupApproximation.Analysis.ConjugateAveragingCriterion
import GroupApproximation.Meta.AxiomGuard

/-!
# Property `P_naive` and Powers' averaging at acylindrically hyperbolic groups

`non_mf_groups_exist.tex`, proof of `cor:regular-nonmf-algebra`, tex lines
1725-1730:

> The group $Q$ is countable, torsion-free, and acylindrically
> hyperbolic, so it contains a non-degenerate hyperbolically embedded
> subgroup~\cite[Theorem~1.2]{Osin} and has no nontrivial finite normal
> subgroup.  Dahmani, Guirardel, and Osin give simplicity and uniqueness
> of the trace~\cite[Theorem~2.35]{DGO}, ...

`naiveFreeProductAtAcylindricallyHyperbolic` proves the closed Prop
`NaiveFreeProductAtAcylindricallyHyperbolic`.  This module spells its conclusion
as the group property `NaiveFreeProductProperty G`, one group at a time, and
feeds it to `powersAveragingEstimate_of_naiveFreeProductProperty`: at a
countable acylindrically hyperbolic group with no nontrivial finite normal
subgroup, Powers' averaging estimate holds.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.NaiveFreeProduct

/-- **Property `P_naive` at a countable acylindrically hyperbolic group with
`K(G) = 1`**, from the closed `naiveFreeProductAtAcylindricallyHyperbolic`. -/
theorem naiveFreeProductProperty_of_isAcylindricallyHyperbolic (G : Type) [Group G]
    [Countable G] [IsAcylindricallyHyperbolic G] (hrad : HasTrivialFiniteRadical G) :
    NaiveFreeProductProperty G :=
  naiveFreeProductAtAcylindricallyHyperbolic G hrad

/-- **Powers' averaging estimate at a countable acylindrically hyperbolic group
with `K(G) = 1`.** -/
theorem powersAveragingEstimate_of_isAcylindricallyHyperbolic (G : Type) [Group G]
    [Countable G] [IsAcylindricallyHyperbolic G] (hrad : HasTrivialFiniteRadical G) :
    ReducedGroupCStarTrace.PowersAveragingEstimate G :=
  ReducedGroupCStarTrace.powersAveragingEstimate_of_naiveFreeProductProperty G
    (naiveFreeProductProperty_of_isAcylindricallyHyperbolic G hrad)

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

#audit_axioms naiveFreeProductProperty_of_isAcylindricallyHyperbolic
#audit_axioms powersAveragingEstimate_of_isAcylindricallyHyperbolic
