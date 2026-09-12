import GroupApproximation.Analysis.CalkinAlgebra
import GroupApproximation.Analysis.CalkinSchauderProof

/-!
# The Calkin algebra's star, unconditionally

`Analysis/CalkinAlgebra` builds `Q(H) = B(H)/K(H)` as a normed complex algebra
outright, and its `Star`, `StarRing` and `StarModule` structure *given*
`CStarQuotient.IsStarIdeal (compactIdeal H)` — that is, given Schauder's
theorem.  `Analysis/CalkinSchauderProof` proves Schauder's theorem, so the
instance can be installed once and for all; this module does that.

After this module `Q(H)` is a normed star algebra with no hypotheses.  What is
still owed before it is a *C-star* algebra, and so before Arveson, Stinespring
and Voiculescu can be stated against it as maps of C-star algebras, is the
quotient C-star identity `CStarQuotient.CStarIdentityStatement`, whose standard
proof runs through an approximate unit of the ideal.

`Analysis/CalkinCStarAlgebra` supersedes this route: it builds `Q(H)` on the
root-imported quotient machinery, which already carries the C-star identity, so
nothing is left owed there.  This module is kept because
`Analysis/CalkinAlgebra`'s opaque `Calkin H` still exists and its star should not
rest on a hypothesis.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated.
-/

namespace GroupApproximation
namespace CalkinAlgebra

noncomputable section

/-- **The compacts are a star-closed ideal.**  Schauder's theorem, in the
instance form `Analysis/CalkinAlgebra` consumes. -/
instance compactIdeal_isStarIdeal (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    CStarQuotient.IsStarIdeal (compactIdeal H) :=
  isStarIdeal_of_compactStarClosed H compactStarClosed

end

end CalkinAlgebra
end GroupApproximation
