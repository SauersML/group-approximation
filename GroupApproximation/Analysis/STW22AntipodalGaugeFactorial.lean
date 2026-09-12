import GroupApproximation.Analysis.STW22TraciallyCompletePair
import GroupApproximation.Analysis.STW22AntipodalNormComparison
import GroupApproximation.Meta.AxiomGuard

/-!
# The antipodal gauge gives a factorial tracially complete pair

This is the instantiation of `Analysis/STW22FactorialCore` and
`Analysis/STW22TraciallyCompletePair` at the concrete antipodal coordinate
gauge, and nothing more.

It deliberately does **not** import `Analysis/STW22ConditionalNegativeSolution`.
The factoriality and tracial-completeness half of STW Problem XXII is the
*hypothesis* of the problem, and it needs no topological input: only the
coordinate norm comparison.  Keeping the two apart means the hypothesis can be
verified while the negative answer's Borsuk--Ulam chain is still being
assembled.

## Every instance argument is supplied by hand

`STW22ConditionalNegativeSolution` measured why this is necessary, and the same
obstruction applies verbatim here.  In an application such as

    designatedTraces antipodalAllTracesGauge_isCoordinateNormComparison

the elaborator reaches the `[∀ n, Nonempty (TracialState (D n))]` binder before
`D` is determined -- the only argument that would determine it is the comparison
datum, whose own type is stated through the gauge abbreviation `G D` -- so the
goal is `∀ n, Nonempty (TracialState (?D n))`, which no registered instance can
solve.  Registering the family is necessary but not sufficient; the `@`-applied
form is what elaborates.  The abbreviations below therefore pin `D` and all
three instances explicitly, and being `abbrev`s they *are* the general
definitions rather than merely equal to them.
-/

namespace GroupApproximation
namespace STW22FactorialCore

open UniformTracialTwoNullIdeal UniformTracialGNSTwoGauge
open UniformTracialBoundedCauchyQuotient
open STW22 STW22ActualTraceSpaces STW22CanonicalTraceExtension
open TraciallyComplete

noncomputable section

set_option linter.unusedSectionVars false

/-- The family of nonempty coordinate trace spaces, passed by hand. -/
abbrev antipodalNonemptyTracialStates :
    ∀ n, Nonempty (TracialState (AntipodalCounterexampleBlock n)) :=
  fun n ↦ nonemptyTracialState_antipodalCounterexampleBlock n

/-- **The designated trace set `X` of the antipodal counterexample's uniform
tracial completion**, with every instance argument pinned. -/
noncomputable abbrev antipodalGaugeDesignatedTraces :=
  @designatedTraces AntipodalCounterexampleBlock inferInstance inferInstance
    antipodalNonemptyTracialStates antipodalCoordinateNormBound
    antipodalAllTracesGauge_isCoordinateNormComparison

/-- The canonical extension map, with every instance argument pinned. -/
noncomputable abbrev antipodalGaugeCanonicalExtension :=
  @canonicalExtension AntipodalCounterexampleBlock inferInstance inferInstance
    antipodalNonemptyTracialStates antipodalCoordinateNormBound
    antipodalAllTracesGauge_isCoordinateNormComparison

/-- **The antipodal pair is tracially complete**, CCEGSTW Definition 3.4: `X` is
nonempty, weak-star compact, convex and faithful, and the unit ball of `M` is
`‖·‖_{2,X}`-complete. -/
theorem antipodalGauge_isTraciallyCompletePair :
    IsTraciallyCompletePair antipodalGaugeDesignatedTraces :=
  @isTraciallyCompletePair_designatedTraces AntipodalCounterexampleBlock
    inferInstance inferInstance antipodalNonemptyTracialStates
    antipodalCoordinateNormBound
    antipodalAllTracesGauge_isCoordinateNormComparison

/-- **The antipodal pair is factorial tracially complete**, CCEGSTW Definitions
3.4 and 3.13: additionally `X` is a *closed face* of `T(M)`.  This is the
hypothesis of STW Problem XXII, and it holds with no hypotheses whatever -- in
particular with no topological input. -/
theorem antipodalGauge_isFactorialTraciallyCompletePair :
    IsFactorialTraciallyCompletePair antipodalGaugeDesignatedTraces :=
  @isFactorialTraciallyCompletePair_designatedTraces AntipodalCounterexampleBlock
    inferInstance inferInstance antipodalNonemptyTracialStates
    antipodalCoordinateNormBound
    antipodalAllTracesGauge_isCoordinateNormComparison

/-- `X` is exactly the set of traces induced from `T(A)`. -/
theorem antipodalGauge_designatedTraces_eq_range :
    antipodalGaugeDesignatedTraces = Set.range antipodalGaugeCanonicalExtension :=
  @designatedTraces_eq_range AntipodalCounterexampleBlock inferInstance
    inferInstance antipodalNonemptyTracialStates antipodalCoordinateNormBound
    antipodalAllTracesGauge_isCoordinateNormComparison

/-- `X` is exactly the set of `‖·‖_{2,X}`-continuous traces on the completion.
CCEGSTW Proposition 3.15 for this pair. -/
theorem mem_antipodalGauge_designatedTraces_iff
    (σ : TracialState (BoundedUniformTwoCompletion antipodalAllTracesGauge
      antipodalCoordinateNormBound
      antipodalAllTracesGauge_isCoordinateNormComparison)) :
    σ ∈ antipodalGaugeDesignatedTraces ↔
      IsUniformTwoContinuousOn antipodalGaugeDesignatedTraces σ :=
  @mem_designatedTraces_iff_isUniformTwoContinuousOn AntipodalCounterexampleBlock
    inferInstance inferInstance antipodalNonemptyTracialStates
    antipodalCoordinateNormBound
    antipodalAllTracesGauge_isCoordinateNormComparison σ

/-- The two forms of CCEGSTW Question 1.1 agree for this pair. -/
theorem antipodalGauge_allTracesUniformTwoContinuous_iff :
    AllTracesUniformTwoContinuous antipodalGaugeDesignatedTraces
      ↔ DesignatedTracesAreAllTraces antipodalGaugeDesignatedTraces :=
  @allTracesUniformTwoContinuous_iff_designatedTracesAreAllTraces'
    AntipodalCounterexampleBlock inferInstance inferInstance
    antipodalNonemptyTracialStates antipodalCoordinateNormBound
    antipodalAllTracesGauge_isCoordinateNormComparison

/-- Failure of the trace problem is exactly non-surjectivity of the canonical
extension.  No topological input is assumed here; the Borsuk--Ulam chain
supplies the hypothesis. -/
theorem antipodalGauge_not_designatedTracesAreAllTraces
    (hns : ¬ Function.Surjective antipodalGaugeCanonicalExtension) :
    ¬ DesignatedTracesAreAllTraces antipodalGaugeDesignatedTraces :=
  @not_designatedTracesAreAllTraces_of_not_surjective
    AntipodalCounterexampleBlock inferInstance inferInstance
    antipodalNonemptyTracialStates antipodalCoordinateNormBound
    antipodalAllTracesGauge_isCoordinateNormComparison hns

/-- The same in the first form of CCEGSTW Question 1.1. -/
theorem antipodalGauge_not_allTracesUniformTwoContinuous
    (hns : ¬ Function.Surjective antipodalGaugeCanonicalExtension) :
    ¬ AllTracesUniformTwoContinuous antipodalGaugeDesignatedTraces := by
  intro h
  exact antipodalGauge_not_designatedTracesAreAllTraces hns
    (antipodalGauge_allTracesUniformTwoContinuous_iff.1 h)

#audit_closed_axioms antipodalGauge_isTraciallyCompletePair
#audit_closed_axioms antipodalGauge_isFactorialTraciallyCompletePair
#audit_closed_axioms antipodalGauge_designatedTraces_eq_range

end

end STW22FactorialCore
end GroupApproximation
