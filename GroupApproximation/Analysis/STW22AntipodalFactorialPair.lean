import GroupApproximation.Analysis.STW22TraciallyCompletePair
import GroupApproximation.Analysis.STW22ConditionalNegativeSolution

/-!
# The antipodal counterexample is a factorial tracially complete pair

The XXII endpoint asserts unitality, separability, nuclearity, Type I, the gauge
identity, Bauer-ness of the trace simplex, compact metrizability of its
boundary, and injectivity but not surjectivity of `canonicalExtension`.  What it
did not assert is the hypothesis of the problem it refutes: that the pair
`(M, X)` is **factorial tracially complete**.  Dropping a hypothesis makes a
counterexample weaker, so without it the endpoint refutes a weaker statement
than STW Problem XXII.

This file closes that gap for the concrete antipodal family.  It instantiates
the general theorems of `Analysis/STW22FactorialCore` and
`Analysis/STW22TraciallyCompletePair` at

    D  = AntipodalCounterexampleBlock,
    G  = antipodalAllTracesGauge,
    r  = antipodalCoordinateNormBound,
    hr = antipodalAllTracesGauge_isCoordinateNormComparison,

and produces the conjunct that the XXII endpoint needs:

    IsFactorialTraciallyCompletePair antipodalDesignatedTraces

together with the identification `antipodalDesignatedTraces = range
canonicalExtension`, which is what stops the new conjunct from being about some
other, conveniently chosen, set of traces.
-/

namespace GroupApproximation
namespace STW22

open UniformTracialTwoNullIdeal UniformTracialGNSTwoGauge
open UniformTracialBoundedCauchyQuotient
open STW22ActualTraceSpaces STW22CanonicalTraceExtension
open TraciallyComplete STW22FactorialCore

noncomputable section

set_option linter.unusedSectionVars false

/-- **The designated traces of the antipodal counterexample.**  By
`antipodalDesignatedTraces_eq_range` this is exactly the set of traces induced
from `T(A)`, i.e. the range of `canonicalExtension`. -/
def antipodalDesignatedTraces :
    Set (TracialState (BoundedUniformTwoCompletion antipodalAllTracesGauge
      antipodalCoordinateNormBound
      antipodalAllTracesGauge_isCoordinateNormComparison)) :=
  designatedTraces antipodalAllTracesGauge_isCoordinateNormComparison

/-- The designated traces are the traces induced from `T(A)`. -/
theorem antipodalDesignatedTraces_eq_range :
    antipodalDesignatedTraces =
      Set.range (canonicalExtension
        antipodalAllTracesGauge_isCoordinateNormComparison) :=
  designatedTraces_eq_range antipodalAllTracesGauge_isCoordinateNormComparison

/-- The designated traces are exactly the uniform-two-continuous traces. -/
theorem mem_antipodalDesignatedTraces_iff
    (σ : TracialState (BoundedUniformTwoCompletion antipodalAllTracesGauge
      antipodalCoordinateNormBound
      antipodalAllTracesGauge_isCoordinateNormComparison)) :
    σ ∈ antipodalDesignatedTraces ↔
      IsUniformTwoContinuousOn antipodalDesignatedTraces σ :=
  mem_designatedTraces_iff_isUniformTwoContinuousOn
    antipodalAllTracesGauge_isCoordinateNormComparison σ

/-- **The antipodal pair is tracially complete**, CCEGSTW Definition 3.4. -/
theorem antipodal_isTraciallyCompletePair :
    IsTraciallyCompletePair antipodalDesignatedTraces :=
  isTraciallyCompletePair_designatedTraces
    antipodalAllTracesGauge_isCoordinateNormComparison

/-- **The antipodal pair is factorial tracially complete**, CCEGSTW Definitions
3.4 and 3.13.  This is the hypothesis of STW Problem XXII. -/
theorem antipodal_isFactorialTraciallyCompletePair :
    IsFactorialTraciallyCompletePair antipodalDesignatedTraces :=
  isFactorialTraciallyCompletePair_designatedTraces
    antipodalAllTracesGauge_isCoordinateNormComparison

/-- **The negative answer, in the vocabulary of the problem.**  With the
complex-coordinate Borsuk--Ulam input, the designated traces of the factorial
tracially complete pair are a proper subset of `T(M)`. -/
theorem antipodal_not_designatedTracesAreAllTraces_of_borsukUlam
    (hBU : ComplexOddMapCommonZero) :
    ¬ DesignatedTracesAreAllTraces antipodalDesignatedTraces :=
  not_designatedTracesAreAllTraces_of_not_surjective
    antipodalAllTracesGauge_isCoordinateNormComparison
    (antipodalCanonicalExtension_not_surjective_of_borsukUlam hBU)

/-- The same in the first form of CCEGSTW Question 1.1: some trace on `M` is
not `‖·‖_{2,X}`-continuous. -/
theorem antipodal_not_allTracesUniformTwoContinuous_of_borsukUlam
    (hBU : ComplexOddMapCommonZero) :
    ¬ AllTracesUniformTwoContinuous antipodalDesignatedTraces := by
  intro h
  exact antipodal_not_designatedTracesAreAllTraces_of_borsukUlam hBU
    ((allTracesUniformTwoContinuous_iff_designatedTracesAreAllTraces'
      antipodalAllTracesGauge_isCoordinateNormComparison).1 h)

/-- **STW Problem XXII, refuted as stated.**  There is a pair `(M, X)` which is
a *factorial tracially complete* C-star algebra, whose designated traces are
exactly the traces induced from `T(A)`, and on which not every trace is
`‖·‖_{2,X}`-continuous -- equivalently, `X ⊊ T(M)`.

This is the conjunction that `STW22NegativeSolution` was missing: the first
component is the hypothesis of the problem, and without it the remaining
components refute a strictly weaker statement. -/
theorem antipodalFactorialNegativeSolutionToProblemXXII_of_borsukUlam
    (hBU : ComplexOddMapCommonZero) :
    IsFactorialTraciallyCompletePair antipodalDesignatedTraces ∧
      antipodalDesignatedTraces =
        Set.range (canonicalExtension
          antipodalAllTracesGauge_isCoordinateNormComparison) ∧
      ¬ AllTracesUniformTwoContinuous antipodalDesignatedTraces ∧
      ¬ DesignatedTracesAreAllTraces antipodalDesignatedTraces :=
  ⟨antipodal_isFactorialTraciallyCompletePair,
    antipodalDesignatedTraces_eq_range,
    antipodal_not_allTracesUniformTwoContinuous_of_borsukUlam hBU,
    antipodal_not_designatedTracesAreAllTraces_of_borsukUlam hBU⟩

end

end STW22
end GroupApproximation
