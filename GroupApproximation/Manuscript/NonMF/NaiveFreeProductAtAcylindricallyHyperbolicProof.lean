import GroupApproximation.Manuscript.NonMF.NaiveFreeProductAtAcylindricallyHyperbolic
import GroupApproximation.GGT.PNaiveAcylindrical

/-!
# Property `P_naive` at the hypothesis of `cor:regular-nonmf-algebra`, proved

`Manuscript/NonMF/NaiveFreeProductAtAcylindricallyHyperbolic` fixes the geometric
half of Dahmani--Guirardel--Osin's Theorem 2.35 as `cor:regular-nonmf-algebra`
consumes it: every countable acylindrically hyperbolic group with no nontrivial
finite normal subgroup has property `P_naive`.  This module proves it.

The proof is Abbott--Dahmani's (arXiv:1610.04143, Theorem 2.3), carried out on
Hull's Cayley graph without a Gromov boundary:
`GGT.PNaive.naiveFreeProduct_of_isAcylindricallyHyperbolic`.

## Manuscript status

The geometric half of *"Dahmani, Guirardel, and Osin give simplicity and
uniqueness of the trace"* (tex line 1728); with the analytic half it closes the
simplicity and unique-trace clauses of `cor:regular-nonmf-algebra`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.NaiveFreeProduct

/-- **Property `P_naive` for every countable acylindrically hyperbolic group with
no nontrivial finite normal subgroup** (Abbott--Dahmani, Theorem 2.3). -/
theorem naiveFreeProductAtAcylindricallyHyperbolic :
    NaiveFreeProductAtAcylindricallyHyperbolic := by
  intro G _instG _instC _instAH hrad F hF
  obtain ⟨y, hy, hinj⟩ := GGT.PNaive.naiveFreeProduct_of_isAcylindricallyHyperbolic G hrad F hF
  exact ⟨y, hy, fun f hf => hinj f hf⟩

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.naiveFreeProductAtAcylindricallyHyperbolic
