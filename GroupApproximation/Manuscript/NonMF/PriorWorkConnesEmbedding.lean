import GroupApproximation.Manuscript.OneSidedMFRadical.ReducedCStarConsequence
import GroupApproximation.Meta.AxiomGuard

/-!
# The Connes-embedding comparison in `Non-MF Groups`

The manuscript recalls that the negative solution of the Connes embedding
problem already implies the existence of a separable stably finite non-MF
`C*`-algebra, and then observes that its own theorem supplies such an algebra
among reduced group `C*`-algebras.

The mathematical conclusion of that comparison is stronger in the present
development: the explicit reduced group algebra constructed by the manuscript
proves both clauses directly.  Thus the historical citation is provenance and
does not enlarge the formal trust surface.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace PriorWork

/-- The conclusion of the manuscript's Connes-embedding comparison: a
separable stably finite non-MF `C*`-algebra exists, and one is the reduced
group `C*`-algebra constructed in the paper. -/
theorem printedNegativeConnesEmbeddingSentence :
    OneSidedMFRadical.SeparableStablyFiniteNonMFCStarAlgebraExists ∧
      OneSidedMFRadical.ReducedCStarConsequence :=
  ⟨OneSidedMFRadical.manuscriptSeparableStablyFiniteNonMFCStarAlgebraExists,
    OneSidedMFRadical.manuscriptReducedCStarConsequence⟩

end PriorWork
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.NonMF.PriorWork.printedNegativeConnesEmbeddingSentence
