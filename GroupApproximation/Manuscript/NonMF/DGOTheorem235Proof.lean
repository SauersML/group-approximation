import GroupApproximation.Manuscript.NonMF.DGO235FromNaiveFreeProduct
import GroupApproximation.Manuscript.NonMF.NaiveFreeProductAtAcylindricallyHyperbolicProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Dahmani--Guirardel--Osin, Theorem 2.35, at the printed hypotheses

`cor:regular-nonmf-algebra` cites Dahmani, Guirardel and Osin for simplicity and
uniqueness of the trace of `C*_r(Q)`, for a countable acylindrically hyperbolic
group with no nontrivial finite normal subgroup (`DGOTheorem235Printed`).

The two halves are proved separately:

* analytic: property `P_naive` gives both conclusions through Powers' averaging
  estimate (`dgoTheorem235Printed_of_naiveFreeProduct`);
* geometric: every such group has property `P_naive`, by Abbott--Dahmani's
  Theorem 2.3 on Hull's Cayley graph
  (`naiveFreeProductAtAcylindricallyHyperbolic`).

This module composes them.

## Manuscript status

The citation *"Dahmani, Guirardel, and Osin give simplicity and uniqueness of the
trace"* in the proof of `cor:regular-nonmf-algebra` (tex line 1728).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

/-- **Dahmani--Guirardel--Osin, Theorem 2.35**, at the hypotheses printed in
`cor:regular-nonmf-algebra`: `C*_r(G)` is simple and has a unique tracial state
for every countable acylindrically hyperbolic group `G` with no nontrivial finite
normal subgroup. -/
theorem dgoTheorem235Printed : DGOTheorem235Printed :=
  dgoTheorem235Printed_of_naiveFreeProduct naiveFreeProductAtAcylindricallyHyperbolic

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.dgoTheorem235Printed
