import GroupApproximation.Analysis.STW22AntipodalGaugeFactorial
import GroupApproximation.Analysis.STW22DesignatedTraces
import GroupApproximation.Analysis.STW22UnconditionalCore
import GroupApproximation.Meta.AxiomGuard

/-!
# The XXII endpoint's pair, in the problem's own words

`Analysis/STW22AntipodalGaugeFactorial` proves that the antipodal uniform
tracial completion is a factorial tracially complete C-star algebra, stated
against the pinned gauge.  `Analysis/STW22DesignatedTraces` names the same set
as `antipodalDesignatedTraces`.  This file identifies the two and restates the
results in that vocabulary, so that the XXII endpoint can quote them directly.

The broader endpoint also asserts regularity of the base algebra, identifies
the all-traces gauge, and proves that canonical extension is injective but not
surjective. Printed STW Problem XXII concerns that uniform tracial completion;
factoriality follows from completion at the full trace space (CCEGSTW
Proposition 3.23(iv)). The factoriality conjunct recorded here also makes the
pair an explicit counterexample to the more general CCEGSTW Question 1.1.
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
3.4 and 3.13: `X` is a closed face of `T(M)`. This is the hypothesis of
CCEGSTW Question 1.1 and a consequence of completing at the full base trace
space in printed STW Problem XXII (CCEGSTW Proposition 3.23(iv)). Here `X`
is the set of canonical extensions of all base traces, not all traces of `M`. -/
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

/-- **The factorial-pair trace problem, CCEGSTW Question 1.1, refuted.**  The pair `(M, X)` is a *factorial
tracially complete* C-star algebra; its designated traces are exactly the
`‖·‖_{2,X}`-continuous traces on `M`; and not every trace on `M` is
`‖·‖_{2,X}`-continuous -- equivalently `X ⊊ T(M)`.

The first conjunct supplies the factorial-pair hypothesis of CCEGSTW
Question 1.1. For printed STW Problem XXII, the completion presentation is
also needed; the Palomar bridge proves that presentation for this witness.

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

/-- **The factorial-pair counterexample, with no hypotheses.**  The
Borsuk--Ulam input is discharged by `complexOddMapCommonZero_unconditional`, so
this is a closed proposition and is gated as one. -/
theorem antipodalFactorialNegativeSolutionToProblemXXII :
    IsFactorialTraciallyCompletePair antipodalDesignatedTraces ∧
      (∀ σ : TracialState AntipodalCompletionAlgebra,
        σ ∈ antipodalDesignatedTraces ↔
          IsUniformTwoContinuousOn antipodalDesignatedTraces σ) ∧
      ¬ AllTracesUniformTwoContinuous antipodalDesignatedTraces ∧
      ¬ DesignatedTracesAreAllTraces antipodalDesignatedTraces :=
  antipodalFactorialNegativeSolutionToProblemXXII_of_borsukUlam
    complexOddMapCommonZero_unconditional

#audit_closed_axioms antipodal_isTraciallyCompletePair
#audit_closed_axioms antipodal_isFactorialTraciallyCompletePair
#audit_axioms antipodalFactorialNegativeSolutionToProblemXXII_of_borsukUlam
#audit_closed_axioms antipodalFactorialNegativeSolutionToProblemXXII

end

end STW22
end GroupApproximation
