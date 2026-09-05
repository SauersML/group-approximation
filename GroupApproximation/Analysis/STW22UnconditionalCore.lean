import GroupApproximation.Analysis.STW22ActualTraceSpaces
import GroupApproximation.Analysis.STW22AntipodalNormComparison
import GroupApproximation.Analysis.STW22BaseUniformTracialGauge
import GroupApproximation.Analysis.STW22CanonicalTraceExtension
import GroupApproximation.Analysis.STW22ConditionalNegativeSolution
import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.ComplexOddMapCommonZero

/-!
# The unconditional operator-algebraic core of the STW XXII counterexample

This file closes the only geometric parameter of the antipodal block package
with the proved complex-coordinate Borsuk--Ulam theorem, and then specializes
the actual bounded uniform-tracial completion endpoint.  Every trace appearing
below is a bundled `TracialState` of the displayed C-star algebra.
-/

namespace GroupApproximation
namespace STW22

open STW22ActualTraceSpaces
open Filter PolarLiftingGeneralCStar
open UniformTracialSequenceCompletion UniformTracialTwoNullIdeal
open UniformTracialBoundedCauchyQuotient
open CuntzPedersenTraceZero STW22Assembly
open STW22CanonicalTraceExtension
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-- The common-zero interface used by the antipodal blocks is a theorem, not
an input. -/
theorem complexOddMapCommonZero_unconditional : ComplexOddMapCommonZero := by
  intro d κ hfinite hdim f hf
  letI : Finite κ := hfinite
  exact complexOddMapCommonZero d κ hdim f hf

/-- The concrete antipodal family supplies the complete coordinate-state
obstruction data with no hypotheses. -/
def antipodalCoordinateStateBlockDataUnconditional :
    CoordinateStateBlockData AntipodalCounterexampleBlock
      antipodalAllTracesGauge :=
  antipodalCoordinateStateBlockData complexOddMapCommonZero_unconditional

/-- The full Sections 5--7 counterexample assembly, specialized to the
actual antipodal blocks, their all-traces gauge, the proved coordinate norm
comparison, and the unconditional coordinate-state data.  Every object in the
conclusion is concrete; there is no block-data or topology hypothesis left. -/
theorem antipodal_stw22_trace_problem_counterexample :
    let B := antipodalCoordinateStateBlockDataUnconditional
    scalarPlusJ antipodalAllTracesGauge =
        {x : BoundedCStarSequence AntipodalCounterexampleBlock |
          IsBoundedUniformTwoApproximable antipodalAllTracesGauge.toUniformTwoGauge
            (unitizedC0Sum AntipodalCounterexampleBlock) x} ∧
      Nonempty (CStarAlgebra (BoundedUniformTwoCompletion
        antipodalAllTracesGauge antipodalCoordinateNormBound
          antipodalAllTracesGauge_isCoordinateNormComparison)) ∧
      B.seq ∈ twoNullIdeal antipodalAllTracesGauge ∧
      B.seq ∉ nullCStarSequenceIdeal AntipodalCounterexampleBlock atTop ∧
      (∃ σ : TracialState (CStarProductCorona AntipodalCounterexampleBlock atTop),
        σ (cStarProductCoronaQuotient AntipodalCounterexampleBlock atTop B.seq) = 1) ∧
      cStarProductCoronaQuotient AntipodalCounterexampleBlock atTop B.seq ∉
        traceZeroSpace (CStarProductCorona AntipodalCounterexampleBlock atTop) ∧
      HasUniformTwoDiscontinuousTracialState antipodalAllTracesGauge ∧
      (∃ (σ : TracialState (BoundedUniformTwoCompletion
          antipodalAllTracesGauge antipodalCoordinateNormBound
            antipodalAllTracesGauge_isCoordinateNormComparison))
        (x : ℕ → BoundedUniformTwoCompletion
          antipodalAllTracesGauge antipodalCoordinateNormBound
            antipodalAllTracesGauge_isCoordinateNormComparison),
        Tendsto (fun N ↦ uniformTwoNorm antipodalAllTracesGauge
          ((realize antipodalAllTracesGauge
            antipodalAllTracesGauge_isCoordinateNormComparison (x N) :
              BoundedCStarSequence AntipodalCounterexampleBlock))) atTop (nhds 0) ∧
        ¬ Tendsto (fun N ↦ σ (x N)) atTop (nhds 0)) := by
  exact stw22_trace_problem_counterexample antipodalAllTracesGauge
    antipodalAllTracesGauge_isCoordinateNormComparison
    antipodalCoordinateStateBlockDataUnconditional

/-- The actual completion of the actual unitized `c₀` base has a bundled
tracial state which is not a uniform-two-continuous extension of a base trace.
This is the literal negative answer to the trace-continuity question.

This and the two statements below are the conditional theorems of
`STW22ConditionalNegativeSolution` with the proved Borsuk--Ulam statement
substituted for their hypothesis. -/
theorem not_everyAntipodalCompletionTraceIsContinuousExtension :
    ¬ EveryCompletionTraceIsContinuousExtension antipodalAllTracesGauge
      antipodalAllTracesGauge_isCoordinateNormComparison :=
  not_everyAntipodalCompletionTraceIsContinuousExtension_of_borsukUlam
    complexOddMapCommonZero_unconditional

/-- The canonical map from the actual base trace space to the actual bounded
uniform-two completion trace space is not surjective. -/
theorem antipodalCanonicalExtension_not_surjective :
    ¬ Function.Surjective (canonicalExtension
      antipodalAllTracesGauge_isCoordinateNormComparison) :=
  antipodalCanonicalExtension_not_surjective_of_borsukUlam
    complexOddMapCommonZero_unconditional

/-- The literal trace-space proper inclusion: the canonical extension map is
an injection but not a surjection. -/
theorem antipodal_trace_space_strict_inclusion :
    Function.Injective (canonicalExtension
      antipodalAllTracesGauge_isCoordinateNormComparison) ∧
    ¬ Function.Surjective (canonicalExtension
      antipodalAllTracesGauge_isCoordinateNormComparison) :=
  antipodal_trace_space_strict_inclusion_of_borsukUlam
    complexOddMapCommonZero_unconditional

#audit_closed_axioms antipodal_stw22_trace_problem_counterexample
#audit_closed_axioms not_everyAntipodalCompletionTraceIsContinuousExtension
#audit_closed_axioms antipodal_trace_space_strict_inclusion

end

end STW22
end GroupApproximation
