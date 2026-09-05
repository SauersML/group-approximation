import GroupApproximation.Analysis.STW22ConditionalNegativeSolution
import GroupApproximation.Analysis.TraciallyCompleteCStar
import GroupApproximation.Meta.AxiomGuard

/-!
# The designated trace set of the antipodal completion

STW Problem XXII is a question about a *pair* `(M, X)`: a tracially complete
C-star algebra together with its designated compact convex set of traces.  The
counterexample's `M` is the bounded uniform-two completion of the antipodal
base algebra and its `X` is the set of canonical extensions of the base traces,
named here.

This file connects the counterexample to CCEGSTW's own vocabulary
(`GroupApproximation/Analysis/TraciallyCompleteCStar.lean`) at the point where
the connection is already proved: `X` is nonempty, and the **second form of
CCEGSTW Question 1.1** -- the inclusion `X ⊆ T(M)` is an equality -- is false.
That form is exactly non-surjectivity of the canonical extension map, which is
what the counterexample establishes.

What is deliberately *not* claimed here is `IsFactorialTraciallyCompletePair X`.
Four of its six fields need work that is not yet in the repository:
`isCompact` and `isConvex` need continuity and affineness of
`canonicalExtension`, and `faithful` and `unitBallComplete` are the substance
of calling `M` a completion at all.  Naming that Prop without proving it is
exactly what this campaign forbids, so it is absent rather than assumed.
-/

namespace GroupApproximation
namespace STW22

open STW22ActualTraceSpaces
open STW22AntipodalBoundaryTraceFunction
open STW22CanonicalTraceExtension
open TraciallyComplete

noncomputable section

/-- The antipodal counterexample's uniform tracial completion `M`. -/
abbrev AntipodalCompletionAlgebra :=
  BoundedUniformTwoCompletion antipodalAllTracesGauge antipodalCoordinateNormBound
    antipodalAllTracesGauge_isCoordinateNormComparison

/-- The **designated trace set** `X ⊆ T(M)`: the canonical extensions of the
tracial states of the base algebra.  This is the `X` of the pair `(M, X)` that
STW Problem XXII asks about. -/
abbrev antipodalDesignatedTraces : Set (TracialState AntipodalCompletionAlgebra) :=
  Set.range antipodalCanonicalExtensionMap

/-- The designated trace set is nonempty: the trace at the point at infinity
extends.  This is CCEGSTW's "implicitly we always imagine `X` to be
non-empty", verified rather than assumed. -/
theorem antipodalDesignatedTraces_nonempty :
    antipodalDesignatedTraces.Nonempty :=
  ⟨_, Set.mem_range_self infinityBaseTracialState⟩

/-- **CCEGSTW Question 1.1, second form, answered negatively.**  The designated
traces of the antipodal completion are not all of its traces.

This is literally `¬ Function.Surjective (canonicalExtension …)` read through
`Set.range_eq_univ`, so it adds no mathematics; what it adds is that the
counterexample now says the thing the problem asks in the problem's own
words. -/
theorem not_designatedTracesAreAllTraces_antipodal
    (hBU : ComplexOddMapCommonZero) :
    ¬ DesignatedTracesAreAllTraces antipodalDesignatedTraces := by
  intro h
  exact antipodalCanonicalExtension_not_surjective_of_borsukUlam hBU
    (Set.range_eq_univ.mp h)

#audit_closed_axioms antipodalDesignatedTraces_nonempty
#audit_axioms not_designatedTracesAreAllTraces_antipodal

end

end STW22
end GroupApproximation
