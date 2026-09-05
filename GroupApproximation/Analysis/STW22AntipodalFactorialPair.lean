import GroupApproximation.Analysis.STW22TraciallyCompletePair
import GroupApproximation.Analysis.STW22DesignatedTraces
import GroupApproximation.Meta.AxiomGuard

/-!
# The antipodal counterexample is a factorial tracially complete pair

The XXII endpoint asserts unitality, separability, nuclearity, Type I, the gauge
identity, Bauer-ness of the trace simplex, compact metrizability of its
boundary, and injectivity but not surjectivity of `canonicalExtension`.  What it
did not assert is the hypothesis of the problem it refutes: that the pair
`(M, X)` is **factorial tracially complete**.  Dropping a hypothesis makes a
counterexample weaker, so without it the endpoint refutes a weaker statement
than STW Problem XXII.

`Analysis/STW22DesignatedTraces` names the pair's `X` as
`antipodalDesignatedTraces = Set.range (canonicalExtension …)` and records that
four of the six fields of `IsFactorialTraciallyCompletePair` were not then
available.  They are now.  This file supplies all six.

The bridge is `STW22FactorialCore.designatedTraces_eq_range`: the range of
`canonicalExtension` is exactly the set of tracial states of the completion
dominated by the completion gauge, and that description is what makes the
closed-face argument (CCEGSTW Proposition 3.23(iv), specialised to `X = T(A)`)
go through.
-/

namespace GroupApproximation
namespace STW22

open UniformTracialTwoNullIdeal UniformTracialGNSTwoGauge
open UniformTracialBoundedCauchyQuotient
open STW22ActualTraceSpaces STW22CanonicalTraceExtension
open TraciallyComplete STW22FactorialCore

noncomputable section

set_option linter.unusedSectionVars false

/-- The designated trace set of `Analysis/STW22DesignatedTraces` -- the range of
`canonicalExtension` -- is exactly the set of tracial states of the completion
dominated by the completion gauge.  Everything below is proved through this
identification, so the new conjuncts are about the same `X` the rest of the
endpoint is about. -/
theorem antipodalDesignatedTraces_eq_designatedTraces :
    antipodalDesignatedTraces =
      designatedTraces antipodalAllTracesGauge_isCoordinateNormComparison :=
  (designatedTraces_eq_range antipodalAllTracesGauge_isCoordinateNormComparison).symm

/-- The designated traces are exactly the `‖·‖_{2,X}`-continuous traces on `M`.
This is CCEGSTW Proposition 3.15 for this pair. -/
theorem mem_antipodalDesignatedTraces_iff
    (σ : TracialState AntipodalCompletionAlgebra) :
    σ ∈ antipodalDesignatedTraces ↔
      IsUniformTwoContinuousOn antipodalDesignatedTraces σ := by
  rw [antipodalDesignatedTraces_eq_designatedTraces]
  exact mem_designatedTraces_iff_isUniformTwoContinuousOn
    antipodalAllTracesGauge_isCoordinateNormComparison σ

/-- **The antipodal pair is tracially complete**, CCEGSTW Definition 3.4: `X` is
nonempty, weak-star compact, convex and faithful, and the unit ball of `M` is
`‖·‖_{2,X}`-complete. -/
theorem antipodal_isTraciallyCompletePair :
    IsTraciallyCompletePair antipodalDesignatedTraces := by
  rw [antipodalDesignatedTraces_eq_designatedTraces]
  exact isTraciallyCompletePair_designatedTraces
    antipodalAllTracesGauge_isCoordinateNormComparison

/-- **The antipodal pair is factorial tracially complete**, CCEGSTW Definitions
3.4 and 3.13: additionally `X` is a *closed face* of `T(M)`.  This is the
hypothesis of STW Problem XXII, and it is a theorem here rather than an
assumption, because `X` is the whole of `T(A)` and a set is a face of itself
(CCEGSTW Proposition 3.23(iv)). -/
theorem antipodal_isFactorialTraciallyCompletePair :
    IsFactorialTraciallyCompletePair antipodalDesignatedTraces := by
  rw [antipodalDesignatedTraces_eq_designatedTraces]
  exact isFactorialTraciallyCompletePair_designatedTraces
    antipodalAllTracesGauge_isCoordinateNormComparison

/-- The two forms of CCEGSTW Question 1.1 agree for this pair. -/
theorem antipodal_allTracesUniformTwoContinuous_iff :
    AllTracesUniformTwoContinuous antipodalDesignatedTraces
      ↔ DesignatedTracesAreAllTraces antipodalDesignatedTraces := by
  rw [antipodalDesignatedTraces_eq_designatedTraces]
  exact allTracesUniformTwoContinuous_iff_designatedTracesAreAllTraces'
    antipodalAllTracesGauge_isCoordinateNormComparison

/-- **CCEGSTW Question 1.1, first form, answered negatively.**  Some trace on
`M` is not `‖·‖_{2,X}`-continuous. -/
theorem antipodal_not_allTracesUniformTwoContinuous_of_borsukUlam
    (hBU : ComplexOddMapCommonZero) :
    ¬ AllTracesUniformTwoContinuous antipodalDesignatedTraces := by
  intro h
  exact not_designatedTracesAreAllTraces_antipodal hBU
    (antipodal_allTracesUniformTwoContinuous_iff.1 h)

/-- **STW Problem XXII, refuted as stated.**  The pair `(M, X)` is a *factorial
tracially complete* C-star algebra whose designated traces are exactly the
traces induced from `T(A)`, and not every trace on `M` is `‖·‖_{2,X}`-continuous
-- equivalently `X ⊊ T(M)`.

The first conjunct is the hypothesis of the problem.  Without it the remaining
conjuncts refute a strictly weaker statement, which is why the endpoint needs
it. -/
theorem antipodalFactorialNegativeSolutionToProblemXXII_of_borsukUlam
    (hBU : ComplexOddMapCommonZero) :
    IsFactorialTraciallyCompletePair antipodalDesignatedTraces ∧
      antipodalDesignatedTraces =
        Set.range (canonicalExtension
          antipodalAllTracesGauge_isCoordinateNormComparison) ∧
      ¬ AllTracesUniformTwoContinuous antipodalDesignatedTraces ∧
      ¬ DesignatedTracesAreAllTraces antipodalDesignatedTraces :=
  ⟨antipodal_isFactorialTraciallyCompletePair, rfl,
    antipodal_not_allTracesUniformTwoContinuous_of_borsukUlam hBU,
    not_designatedTracesAreAllTraces_antipodal hBU⟩

#audit_closed_axioms antipodal_isTraciallyCompletePair
#audit_closed_axioms antipodal_isFactorialTraciallyCompletePair
#audit_closed_axioms antipodalDesignatedTraces_eq_designatedTraces
#audit_axioms antipodalFactorialNegativeSolutionToProblemXXII_of_borsukUlam

end

end STW22
end GroupApproximation
