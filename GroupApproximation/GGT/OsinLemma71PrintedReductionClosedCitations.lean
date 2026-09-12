import GroupApproximation.GGT.OsinLemma71PrintedReduction
import GroupApproximation.Manuscript.NonMF.DGOTheorem235Proof
import GroupApproximation.Manuscript.NonMF.GerasimovaOsinTheorem11Closed
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:regular-nonmf-algebra` over the printed citations, C⋆-algebraic inputs discharged

`OsinPrinted.manuscriptRegularNonMFAlgebra_of_citations_of_smallCancellation` states
`cor:regular-nonmf-algebra` over the literature inputs, Hull's small cancellation
theorem as printed, and the two C⋆-algebraic citations of the printed proof.  Both
of those are proved (`TorsionFreePrinted.dgoTheorem235Printed`,
`TorsionFreePrinted.gerasimovaOsinTheorem11Printed`), and this twin discharges them.
-/

namespace GroupApproximation
namespace GGT
namespace OsinPrinted

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.Manuscript.NonMF.TheoremC

/-- **`cor:regular-nonmf-algebra` over the printed citations**, with Osin's Lemma 7.1
and both C⋆-algebraic citations discharged. -/
theorem manuscriptRegularNonMFAlgebra_of_citations_of_smallCancellation_closedCitations
    (I : LiteratureInputs) (hW : FinitelyPresentedInfiniteSimpleStatement)
    (h : HullSmallCancellationPrinted.{0}) : PrintedRegularNonMFAlgebra :=
  manuscriptRegularNonMFAlgebra_of_citations_of_smallCancellation I hW h
    dgoTheorem235Printed gerasimovaOsinTheorem11Printed

end OsinPrinted
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.OsinPrinted.manuscriptRegularNonMFAlgebra_of_citations_of_smallCancellation_closedCitations
