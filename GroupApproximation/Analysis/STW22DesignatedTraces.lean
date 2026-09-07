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

`IsFactorialTraciallyCompletePair X` is not claimed here either, but the reason
has changed and the note that used to stand in this place is no longer true.  It
recorded four of the six fields as work "not yet in the repository":
`isCompact` and `isConvex` waiting on continuity and affineness of
`canonicalExtension`, `faithful` and `unitBallComplete` on the substance of
calling `M` a completion at all.  All four are now proved, and the Prop itself
is a theorem for exactly the `X` this file names:

* `STW22FactorialCore.isCompact_designatedTraces`,
  `isConvexTraceSet_designatedTraces`, `isClosed_designatedTraces` and
  `isFaceTraceSet_designatedTraces` -- compactness through weak-star compactness
  of the trace space, and the face condition through CCEGSTW Proposition
  3.23(iv) at `X = T(A)`;
* `STW22TraciallyCompletePair.isFaithfulTraceSet_designatedTraces` and
  `unitBallUniformTwoComplete_designatedTraces` -- faithfulness turned out to
  need no extra hypothesis, because the coordinate norm comparison already
  forces a gauge-null element to vanish coordinatewise;
* `STW22AntipodalFactorialPair.antipodal_isFactorialTraciallyCompletePair` --
  the assembled Prop, for `antipodalDesignatedTraces` as defined below.

So the Prop is absent from this file because it belongs upstream of it, not
because it is open.  This file's job is to name `X`.
-/

namespace GroupApproximation
namespace STW22

open STW22ActualTraceSpaces
open STW22AntipodalBoundaryTraceFunction
open STW22CanonicalTraceExtension
open TraciallyComplete
open UniformTracialBoundedCauchyQuotient

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
  ⟨antipodalCanonicalExtensionMap infinityBaseTracialState,
    Set.mem_range_self infinityBaseTracialState⟩

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
