import GroupApproximation.Manuscript.OneSidedMFRadical.SimplifiedCoefficientSeparation
import GroupApproximation.Meta.AxiomGuard

/-!
# Closed audit of the current coefficient-separation proof

The current manuscript uses two sandwich factorizations and the explicit
witnesses `a = d t₁ u`, `b = v s₀ c`.  The imported module formalizes each of
its three displayed calculations and their assembly.  These audits ensure that
the current route, rather than the superseded four-factorization route, is
hypothesis-free.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

#audit_closed_axioms manuscriptPrintedSimplifiedSeparationWitnessesAnnihilate
#audit_closed_axioms manuscriptPrintedSimplifiedSeparationReversedProduct
#audit_closed_axioms manuscriptPrintedSimplifiedSeparationVanishingImplication
#audit_closed_axioms manuscriptPrintedSimplifiedCoefficientSeparationRecipe
#audit_closed_axioms manuscriptPrintedSimplifiedCoefficientSeparation
#audit_closed_axioms manuscriptPrintedSimplifiedCoefficientSeparationAtBinaryLeavitt
#audit_closed_axioms manuscriptPrintedSimplifiedCoefficientSeparationCalculations

end OneSidedMFRadical
end Manuscript
end GroupApproximation
