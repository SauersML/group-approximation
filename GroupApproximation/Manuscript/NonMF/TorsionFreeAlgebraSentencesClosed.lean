import GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences
import GroupApproximation.Manuscript.NonMF.DGOTheorem235Proof
import GroupApproximation.Manuscript.NonMF.GerasimovaOsinTheorem11Closed
import GroupApproximation.Meta.AxiomGuard

/-!
# The C⋆-algebraic sentence of `cor:regular-nonmf-algebra`, closed

`non_mf_groups_exist.tex`, proof of `cor:regular-nonmf-algebra` (tex lines
1728–1731):

> Dahmani, Guirardel, and Osin give simplicity and uniqueness of the trace
> [DGO, Theorem 2.35], and Gerasimova and Osin give density of the invertible
> elements, which is stable rank one [GO, Theorem 1.1].

`TorsionFreePrintedSentences.manuscriptSentence_algebraSimpleUniqueTraceStableRank`
applies the two citations at the hypotheses the previous sentence supplies, with the
citations as hypotheses.  Both are proved: `TorsionFreePrinted.dgoTheorem235Printed`
from the naive free-product property of acylindrically hyperbolic groups with
trivial finite radical, and `TorsionFreePrinted.gerasimovaOsinTheorem11Printed`.  This
module is the sentence with both discharged.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrintedSentences

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.ReducedGroupCStarTrace

/-- **"Dahmani, Guirardel, and Osin give simplicity and uniqueness of the trace,
and Gerasimova and Osin give density of the invertible elements, which is stable
rank one."**  Both citations proved. -/
theorem manuscriptSentence_algebraSimpleUniqueTraceStableRank_closed
    (Q : Type) [Group Q] [Countable Q] [IsAcylindricallyHyperbolic Q]
    (hQ : IsPowerTorsionFree Q) :
    IsSimpleCStar (ReducedGroupCStar Q) ∧
      HasUniqueTracialState (ReducedGroupCStar Q) ∧
        IsStableRankOne (ReducedGroupCStar Q) :=
  manuscriptSentence_algebraSimpleUniqueTraceStableRank dgoTheorem235Printed
    gerasimovaOsinTheorem11Printed Q hQ

end TorsionFreePrintedSentences
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_algebraSimpleUniqueTraceStableRank_closed
