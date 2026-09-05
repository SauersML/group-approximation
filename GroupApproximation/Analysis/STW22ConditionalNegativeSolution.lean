import GroupApproximation.Analysis.STW22ActualTraceSpaces
import GroupApproximation.Analysis.STW22AntipodalNormComparison
import GroupApproximation.Analysis.STW22AntipodalTraceSimplexBauer
import GroupApproximation.Analysis.STW22BaseAlgebraNuclear
import GroupApproximation.Analysis.STW22BaseUniformTracialGauge
import GroupApproximation.Analysis.STW22CanonicalTraceExtension
import GroupApproximation.Meta.AxiomGuard

/-!
# The STW Problem XXII counterexample, with its one topological input explicit

This file assembles the complete negative solution to STW Problem XXII from the
concrete antipodal blocks, taking the complex-coordinate Borsuk--Ulam statement
`ComplexOddMapCommonZero` as an **explicit argument** rather than importing its
proof.

The point of the separation is that everything here is operator-algebraic and
compiles against the part of the sphere-degree development that is already in
the root import graph.  The complete Borsuk--Ulam closure lives behind a
several-hundred-module algebraic-topology port; keeping it out of this file's
imports means the operator-algebraic half of the counterexample is verified and
axiom-audited on its own, and the unconditional endpoint in
`STW22NegativeSolution` is then a one-line substitution of the proved
`complexOddMapCommonZero_unconditional` for `hBU`.

`ComplexOddMapCommonZero` therefore appears in no exported statement of the
final endpoint: it is discharged there, not assumed.
-/

namespace GroupApproximation
namespace STW22

open CStarExactness
open STW22ActualTraceSpaces
open STW22AntipodalBoundaryTraceFunction
open STW22AntipodalTraceSimplexBauer
open STW22BaseAlgebraNuclear
open STW22BaseAlgebraUnitization
open STW22CanonicalTraceExtension
open TopologicalSpace

open scoped NNReal

noncomputable section

universe v

/-- The sequence-model gauge used throughout is exactly the supremum of the
two-norms coming from all bundled tracial states of the actual base algebra.
No topological input is involved. -/
theorem antipodalBaseTracialTwoSize_eq_completionGauge
    (x : BaseAlgebra AntipodalCounterexampleBlock) :
    STW22BaseUniformTracialGauge.baseTracialTwoSize x =
      STW22Assembly.uniformTwoNorm antipodalAllTracesGauge x.1 := by
  simpa only [antipodalAllTracesGauge] using
    STW22BaseUniformTracialGauge.baseTracialTwoSize_eq_uniformTwoNorm_allTraces x

/-- The canonical map from the actual base trace space to the actual bounded
uniform-two completion trace space is injective.  This half of the proper
inclusion needs no topological input at all: it is inverted by restriction. -/
theorem antipodalCanonicalExtension_injective :
    Function.Injective (canonicalExtension
      antipodalAllTracesGauge_isCoordinateNormComparison) := by
  simpa only [antipodalAllTracesGauge] using
    (canonicalExtension_injective
      antipodalAllTracesGauge_isCoordinateNormComparison)

/-- Given the complex-coordinate Borsuk--Ulam statement, the actual completion
of the actual unitized `c₀` base has a bundled tracial state which is not a
uniform-two-continuous extension of a base trace. -/
theorem not_everyAntipodalCompletionTraceIsContinuousExtension_of_borsukUlam
    (hBU : ComplexOddMapCommonZero) :
    ¬ EveryCompletionTraceIsContinuousExtension antipodalAllTracesGauge
      antipodalAllTracesGauge_isCoordinateNormComparison :=
  not_everyCompletionTraceIsContinuousExtension_of_blockData
    antipodalAllTracesGauge
    antipodalAllTracesGauge_isCoordinateNormComparison
    (antipodalCoordinateStateBlockData hBU)

/-- Given the complex-coordinate Borsuk--Ulam statement, the canonical
extension map is not surjective. -/
theorem antipodalCanonicalExtension_not_surjective_of_borsukUlam
    (hBU : ComplexOddMapCommonZero) :
    ¬ Function.Surjective (canonicalExtension
      antipodalAllTracesGauge_isCoordinateNormComparison) := by
  simpa only [antipodalAllTracesGauge] using
    canonicalExtension_not_surjective_of_not_every
      antipodalAllTracesGauge_isCoordinateNormComparison
      (not_everyAntipodalCompletionTraceIsContinuousExtension_of_borsukUlam hBU)

/-- The literal trace-space proper inclusion `T(A) ⊊ T(M)`, with the
topological input explicit. -/
theorem antipodal_trace_space_strict_inclusion_of_borsukUlam
    (hBU : ComplexOddMapCommonZero) :
    Function.Injective (canonicalExtension
      antipodalAllTracesGauge_isCoordinateNormComparison) ∧
    ¬ Function.Surjective (canonicalExtension
      antipodalAllTracesGauge_isCoordinateNormComparison) :=
  ⟨antipodalCanonicalExtension_injective,
    antipodalCanonicalExtension_not_surjective_of_borsukUlam hBU⟩

/-- **Negative solution to STW Problem XXII, with the topological input
explicit.**

The literal counterexample is unital, separable, nuclear, and Type I.  Its
actual pointwise weak-star trace simplex is nonempty and Bauer, its actual
extreme-boundary subtype is compact metrizable, the completion gauge is
literally the supremum over all base traces, and canonical extension from base
traces to completion traces is injective but not surjective.

The only hypothesis is `hBU`, the complex-coordinate Borsuk--Ulam statement,
which is a theorem of the sphere-degree development; `STW22NegativeSolution`
supplies it and states the same conclusion with no hypothesis at all. -/
theorem negativeSolutionToProblemXXII_of_borsukUlam
    (hBU : ComplexOddMapCommonZero) :
    Nonempty (CStarAlgebra (BaseAlgebra AntipodalCounterexampleBlock)) ∧
      TopologicalSpace.SeparableSpace (BaseAlgebra AntipodalCounterexampleBlock) ∧
      IsNuclearCStarAlgebra (BaseAlgebra AntipodalCounterexampleBlock) ∧
      IsTypeI.{0, v} (BaseAlgebra AntipodalCounterexampleBlock) ∧
      (∀ x : BaseAlgebra AntipodalCounterexampleBlock,
        STW22BaseUniformTracialGauge.baseTracialTwoSize x =
          STW22Assembly.uniformTwoNorm antipodalAllTracesGauge x.1) ∧
      Set.Nonempty antipodalWeakStarTraceSimplex ∧
      IsBauerSimplex ℝ≥0 antipodalWeakStarTraceSimplex ∧
      (CompactSpace AntipodalWeakStarExtremeBoundary ∧
        MetrizableSpace AntipodalWeakStarExtremeBoundary) ∧
      Function.Injective (canonicalExtension
        antipodalAllTracesGauge_isCoordinateNormComparison) ∧
      ¬ Function.Surjective (canonicalExtension
        antipodalAllTracesGauge_isCoordinateNormComparison) :=
  ⟨⟨inferInstance⟩,
    separableSpace_baseAlgebra_antipodalCounterexampleBlock,
    isNuclearCStarAlgebra_baseAlgebra_antipodalCounterexampleBlock,
    isTypeI_baseAlgebra_antipodalCounterexampleBlock,
    antipodalBaseTracialTwoSize_eq_completionGauge,
    ⟨tracialStateEvaluation infinityBaseTracialState,
      infinityBaseTracialState, rfl⟩,
    isBauerSimplex_antipodalWeakStarTraceSimplex,
    antipodalWeakStarExtremeBoundary_compact_metrizable,
    antipodalCanonicalExtension_injective,
    antipodalCanonicalExtension_not_surjective_of_borsukUlam hBU⟩

-- `antipodalBaseTracialTwoSize_eq_completionGauge` is universally quantified over
-- the algebra element, so its type is a `∀` and the closed-endpoint gate would
-- reject it on that ground alone; the axiom audit is the applicable one.
#audit_axioms antipodalBaseTracialTwoSize_eq_completionGauge
#audit_closed_axioms antipodalCanonicalExtension_injective
#audit_axioms not_everyAntipodalCompletionTraceIsContinuousExtension_of_borsukUlam
#audit_axioms antipodal_trace_space_strict_inclusion_of_borsukUlam
#audit_axioms negativeSolutionToProblemXXII_of_borsukUlam

end

end STW22
end GroupApproximation
