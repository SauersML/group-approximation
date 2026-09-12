import GroupApproximation.Algebra.NaiveFreeProductProperty
import GroupApproximation.Manuscript.NonMF.AcylindricallyHyperbolic
import GroupApproximation.Manuscript.NonMF.TorsionFreeRelativeQuotient

/-!
# Property `P_naive` at the hypotheses of `cor:regular-nonmf-algebra`

The printed proof of `cor:regular-nonmf-algebra` reads:

> The group `Q` is countable, torsion-free, and acylindrically hyperbolic, so it
> contains a non-degenerate hyperbolically embedded subgroup and has no
> nontrivial finite normal subgroup.  Dahmani, Guirardel, and Osin give
> simplicity and uniqueness of the trace [DGO, Theorem 2.35] …

`DGOTheorem235Printed` (`Manuscript/NonMF/RegularNonMFAlgebra`) carries that
citation at exactly these hypotheses: a countable acylindrically hyperbolic group
with trivial finite radical.  The route to it chosen here goes through property
`P_naive` (`Algebra/NaiveFreeProductProperty`), which Abbott and Dahmani prove at
the same hypotheses.  This module names that statement, so that the geometric
producer and the analytic consumer meet at one Prop:

* producer: a proof of `NaiveFreeProductAtAcylindricallyHyperbolic`;
* consumer: `NaiveFreeProductProperty G → PowersAveragingEstimate G`, which gives
  `IsSimpleCStar (ReducedGroupCStar G)` and `HasUniqueTracialState
  (ReducedGroupCStar G)`, hence `DGOTheorem235Printed`.

The quantifier shape is `DGOTheorem235Printed`'s, verbatim.

## Manuscript status

Interface statement for `cor:regular-nonmf-algebra`; certifies no printed
sentence on its own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.NaiveFreeProduct

/-- **Abbott–Dahmani's property `P_naive` at the hypotheses of
`DGOTheorem235Printed`.**  Every countable acylindrically hyperbolic group with
no nontrivial finite normal subgroup has `NaiveFreeProductProperty`. -/
def NaiveFreeProductAtAcylindricallyHyperbolic : Prop :=
  ∀ (G : Type) [Group G] [Countable G] [IsAcylindricallyHyperbolic G],
    HasTrivialFiniteRadical G → NaiveFreeProductProperty G

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

#audit_axioms NaiveFreeProductAtAcylindricallyHyperbolic
