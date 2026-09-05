import GroupApproximation.Analysis.STW22AntipodalGaugeFactorial
import GroupApproximation.Analysis.STW22DesignatedTraces
import GroupApproximation.Meta.AxiomGuard

/-!
# The XXII endpoint's pair, in the problem's own words

`Analysis/STW22AntipodalGaugeFactorial` proves that the antipodal uniform
tracial completion is a factorial tracially complete C-star algebra, stated
against the pinned gauge.  `Analysis/STW22DesignatedTraces` names the same set
as `antipodalDesignatedTraces`.  This file identifies the two and restates the
results in that vocabulary, so that the XXII endpoint can quote them directly.

The endpoint asserts unitality, separability, nuclearity, Type I, the gauge
identity, Bauer-ness of the trace simplex, compact metrizability of its
boundary, and injectivity but not surjectivity of the canonical extension.  What
it did not assert is the hypothesis of the problem it refutes: that the pair
`(M, X)` is factorial tracially complete.  Dropping a hypothesis makes a
counterexample weaker, so without it the endpoint refutes a weaker statement
than STW Problem XXII.  `antipodal_isFactorialTraciallyCompletePair` is the
missing conjunct.
-/

namespace GroupApproximation
namespace STW22

open UniformTracialTwoNullIdeal UniformTracialGNSTwoGauge
open UniformTracialBoundedCauchyQuotient
open STW22ActualTraceSpaces STW22CanonicalTraceExtension
open TraciallyComplete STW22FactorialCore

noncomputable section

set_option linter.unusedSectionVars false

/-- The two names for `X` agree: the range of the canonical extension is the set
of tracial states dominated by the completion gauge.  Everything below is proved
through this identification, so the new conjuncts are about the same `X` the
rest of the endpoint is about. -/
theorem antipodalDesignatedTraces_eq_gauge :
    antipodalDesignatedTraces = antipodalGaugeDesignatedTraces :=
  antipodalGauge_designatedTraces_eq_range.symm

/-- **The antipodal pair is tracially complete**, CCEGSTW Definition 3.4. -/
theorem antipodal_isTraciallyCompletePair :
    IsTraciallyCompletePair antipodalDesignatedTraces := by
  rw [antipodalDesignatedTraces_eq_gauge]
  exact antipodalGauge_isTraciallyCompletePair

/-- **The antipodal pair is factorial tracially complete**, CCEGSTW Definitions
3.4 and 3.13: `X` is a closed face of `T(M)`.  This is the hypothesis of STW
Problem XXII, and it is a theorem here rather than an assumption, because `X` is
the whole of `T(A)` and a set is a face of itself (CCEGSTW Proposition
3.23(iv)). -/
theorem antipodal_isFactorialTraciallyCompletePair :
    IsFactorialTraciallyCompletePair antipodalDesignatedTraces := by
  rw [antipodalDesignatedTraces_eq_gauge]
  exact antipodalGauge_isFactorialTraciallyCompletePair

/-- `X` is exactly the set of `‖·‖_{2,X}`-continuous traces.  CCEGSTW
Proposition 3.15 for this pair. -/
theorem mem_antipodalDesignatedTraces_iff
    (σ : TracialState AntipodalCompletionAlgebra) :
    σ ∈ antipodalDesignatedTraces ↔
      IsUniformTwoContinuousOn antipodalDesignatedTraces σ := by
  rw [antipodalDesignatedTraces_eq_gauge]
  exact mem_antipodalGauge_designatedTraces_iff σ

/-- **CCEGSTW Question 1.1, first form, answered negatively.**  Some trace on
`M` is not `‖·‖_{2,X}`-continuous. -/
theorem antipodal_not_allTracesUniformTwoContinuous_of_borsukUlam
    (hBU : ComplexOddMapCommonZero) :
    ¬ AllTracesUniformTwoContinuous antipodalDesignatedTraces := by
  rw [antipodalDesignatedTraces_eq_gauge]
  exact antipodalGauge_not_allTracesUniformTwoContinuous
    (antipodalCanonicalExtension_not_surjective_of_borsukUlam hBU)

/-- **STW Problem XXII, refuted as stated.**  The pair `(M, X)` is a *factorial
tracially complete* C-star algebra; its designated traces are exactly the
`‖·‖_{2,X}`-continuous traces on `M`; and not every trace on `M` is
`‖·‖_{2,X}`-continuous -- equivalently `X ⊊ T(M)`.

The first conjunct is the hypothesis of the problem.  Without it the remaining
conjuncts refute a strictly weaker statement, which is why the endpoint needs
it.

The second conjunct is not decoration.  `X` is *defined* as the range of the
canonical extension, so a conjunct saying so would be `rfl` and would certify
nothing; what needs proof -- and is CCEGSTW Proposition 3.15 -- is that this
range is exactly the set of `‖·‖_{2,X}`-continuous traces.  That is what makes
the third and fourth conjuncts two readings of the *same* failure. -/
theorem antipodalFactorialNegativeSolutionToProblemXXII_of_borsukUlam
    (hBU : ComplexOddMapCommonZero) :
    IsFactorialTraciallyCompletePair antipodalDesignatedTraces ∧
      (∀ σ : TracialState AntipodalCompletionAlgebra,
        σ ∈ antipodalDesignatedTraces ↔
          IsUniformTwoContinuousOn antipodalDesignatedTraces σ) ∧
      ¬ AllTracesUniformTwoContinuous antipodalDesignatedTraces ∧
      ¬ DesignatedTracesAreAllTraces antipodalDesignatedTraces :=
  ⟨antipodal_isFactorialTraciallyCompletePair,
    mem_antipodalDesignatedTraces_iff,
    antipodal_not_allTracesUniformTwoContinuous_of_borsukUlam hBU,
    not_designatedTracesAreAllTraces_antipodal hBU⟩

#audit_closed_axioms antipodal_isTraciallyCompletePair
#audit_closed_axioms antipodal_isFactorialTraciallyCompletePair
#audit_axioms antipodalFactorialNegativeSolutionToProblemXXII_of_borsukUlam

end

end STW22
end GroupApproximation
