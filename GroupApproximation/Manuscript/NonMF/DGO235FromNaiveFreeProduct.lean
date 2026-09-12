import GroupApproximation.Manuscript.NonMF.DGO235UniqueTraceFromAveraging
import GroupApproximation.Manuscript.NonMF.NaiveFreeProductAtAcylindricallyHyperbolic
import GroupApproximation.Analysis.ConjugateAveragingCriterion

/-!
# Dahmani--Guirardel--Osin, Theorem 2.35, from property `P_naive`

The printed proof of `cor:regular-nonmf-algebra` cites Dahmani, Guirardel and Osin
for simplicity and uniqueness of the trace of `C*_r(Q)`.  The manuscript cites the
theorem, not its proof, so any proof of the statement at the printed hypotheses
discharges the citation.  This module assembles one from two parts.

* **Analytic, closed.**  `P_naive` for `G` gives Powers' averaging estimate for
  `C*_r(G)` (`Analysis/ConjugateAveragingCriterion`), and the averaging estimate
  gives both simplicity and a unique tracial state
  (`simpleUniqueTrace_of_powersAveragingEstimate`).  No classical C⋆-algebra
  theorem is used: not Powers, not Akemann--Lee, not
  Breuillard--Kalantar--Kennedy--Ozawa.
* **Geometric, named.**  `NaiveFreeProductAtAcylindricallyHyperbolic`, Abbott and
  Dahmani's theorem at the printed hypotheses.

So `dgoTheorem235Printed_of_naiveFreeProduct` turns a proof of the geometric Prop
into a closed `DGOTheorem235Printed`.

## Manuscript status

Reduction step for `cor:regular-nonmf-algebra` (the sentence "Dahmani, Guirardel,
and Osin give simplicity and uniqueness of the trace"); certifies the sentence
once the geometric Prop has a producer.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.ReducedGroupCStarTrace
open GroupApproximation.NaiveFreeProduct

/-- **Both clauses of DGO 2.35 from property `P_naive`**, at any group. -/
theorem simpleUniqueTrace_of_naiveFreeProductProperty (G : Type) [Group G]
    (h : NaiveFreeProductProperty G) :
    IsSimpleCStar (ReducedGroupCStar G) ∧ HasUniqueTracialState (ReducedGroupCStar G) :=
  simpleUniqueTrace_of_powersAveragingEstimate G
    (powersAveragingEstimate_of_naiveFreeProductProperty G h)

/-- **`DGOTheorem235Printed` from Abbott--Dahmani's `P_naive` at the printed
hypotheses.** -/
theorem dgoTheorem235Printed_of_naiveFreeProduct
    (h : NaiveFreeProductAtAcylindricallyHyperbolic) : DGOTheorem235Printed := by
  intro G instG instC instAH hrad
  letI := instG
  letI := instC
  letI := instAH
  exact simpleUniqueTrace_of_naiveFreeProductProperty G (h G hrad)

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

#audit_axioms simpleUniqueTrace_of_naiveFreeProductProperty
#audit_axioms dgoTheorem235Printed_of_naiveFreeProduct
