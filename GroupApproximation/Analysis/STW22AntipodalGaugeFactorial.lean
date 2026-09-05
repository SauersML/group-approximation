import GroupApproximation.Analysis.STW22TraciallyCompletePair
import GroupApproximation.Analysis.STW22AntipodalNormComparison
import GroupApproximation.Meta.AxiomGuard

/-!
# The antipodal gauge gives a factorial tracially complete pair

This is the instantiation of `Analysis/STW22FactorialCore` and
`Analysis/STW22TraciallyCompletePair` at the concrete antipodal coordinate
gauge, and nothing more.

It deliberately does **not** import `Analysis/STW22ConditionalNegativeSolution`.
That module is currently red (nine `∀ n, Nonempty (TracialState
(AntipodalCounterexampleBlock n))` synthesis failures, and four declarations
poisoned with `sorryAx` as a result), and the point of this file is that the
factoriality and tracial-completeness half of STW Problem XXII does not depend
on it: the topological Borsuk--Ulam input enters only in the *negative answer*,
not in the *hypothesis* of the problem.

`Analysis/STW22AntipodalFactorialPair` transports these statements onto
`STW22.antipodalDesignatedTraces` once that chain compiles.
-/

namespace GroupApproximation
namespace STW22FactorialCore

open UniformTracialTwoNullIdeal UniformTracialGNSTwoGauge
open UniformTracialBoundedCauchyQuotient
open STW22 STW22ActualTraceSpaces STW22CanonicalTraceExtension
open TraciallyComplete

noncomputable section

set_option linter.unusedSectionVars false

/-- **The antipodal pair is tracially complete**, CCEGSTW Definition 3.4. -/
theorem antipodalGauge_isTraciallyCompletePair :
    IsTraciallyCompletePair
      (designatedTraces antipodalAllTracesGauge_isCoordinateNormComparison) :=
  isTraciallyCompletePair_designatedTraces
    antipodalAllTracesGauge_isCoordinateNormComparison

/-- **The antipodal pair is factorial tracially complete**, CCEGSTW Definitions
3.4 and 3.13.  This is the hypothesis of STW Problem XXII, and it holds with no
hypotheses whatever -- in particular with no topological input. -/
theorem antipodalGauge_isFactorialTraciallyCompletePair :
    IsFactorialTraciallyCompletePair
      (designatedTraces antipodalAllTracesGauge_isCoordinateNormComparison) :=
  isFactorialTraciallyCompletePair_designatedTraces
    antipodalAllTracesGauge_isCoordinateNormComparison

/-- The designated traces are exactly the traces induced from `T(A)`. -/
theorem antipodalGauge_designatedTraces_eq_range :
    designatedTraces antipodalAllTracesGauge_isCoordinateNormComparison
      = Set.range (canonicalExtension
          antipodalAllTracesGauge_isCoordinateNormComparison) :=
  designatedTraces_eq_range antipodalAllTracesGauge_isCoordinateNormComparison

/-- The designated traces are exactly the `‖·‖_{2,X}`-continuous traces on the
completion.  CCEGSTW Proposition 3.15 for this pair. -/
theorem mem_antipodalGauge_designatedTraces_iff
    (σ : TracialState (BoundedUniformTwoCompletion antipodalAllTracesGauge
      antipodalCoordinateNormBound
      antipodalAllTracesGauge_isCoordinateNormComparison)) :
    σ ∈ designatedTraces antipodalAllTracesGauge_isCoordinateNormComparison ↔
      IsUniformTwoContinuousOn
        (designatedTraces antipodalAllTracesGauge_isCoordinateNormComparison) σ :=
  mem_designatedTraces_iff_isUniformTwoContinuousOn
    antipodalAllTracesGauge_isCoordinateNormComparison σ

/-- Failure of the trace problem is exactly non-surjectivity of the canonical
extension, with no topological input assumed here. -/
theorem antipodalGauge_not_designatedTracesAreAllTraces
    (hns : ¬ Function.Surjective (canonicalExtension
      antipodalAllTracesGauge_isCoordinateNormComparison)) :
    ¬ DesignatedTracesAreAllTraces
      (designatedTraces antipodalAllTracesGauge_isCoordinateNormComparison) :=
  not_designatedTracesAreAllTraces_of_not_surjective
    antipodalAllTracesGauge_isCoordinateNormComparison hns

#audit_closed_axioms antipodalGauge_isTraciallyCompletePair
#audit_closed_axioms antipodalGauge_isFactorialTraciallyCompletePair
#audit_closed_axioms antipodalGauge_designatedTraces_eq_range

end

end STW22FactorialCore
end GroupApproximation
