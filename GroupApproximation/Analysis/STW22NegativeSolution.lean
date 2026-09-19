import GroupApproximation.Analysis.STW22AntipodalTraceSimplexBauer
import GroupApproximation.Analysis.STW22BaseAlgebraNuclear
import GroupApproximation.Analysis.STW22UnconditionalCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Negative solution to STW Problem XXII

This is the final public endpoint for the antipodal counterexample.  The
concrete algebra is the scalar-plus-`c₀` algebra built from the antipodal
real-projective blocks.  Its C-star-algebra instance supplies unitality, and
the imported concrete theorems supply separability, nuclearity, Type I in
every representation universe, compact metrizability of the trace-boundary
space, and the proper inclusion of trace spaces under canonical extension.

The probability-measure classification of the base trace space and its
concrete extreme-boundary homeomorphism supply the Bauer conclusion.  No
abstract trace-classification hypothesis is introduced here.
-/

namespace GroupApproximation
namespace STW22NegativeSolution

open STW22
open STW22ActualTraceSpaces
open STW22AntipodalTraceBoundary
open STW22AntipodalBoundaryTraceFunction
open STW22AntipodalTraceSimplexBauer
open STW22BaseAlgebraUnitization
open STW22BaseAlgebraNuclear
open STW22CanonicalTraceExtension
open CStarExactness
open TopologicalSpace

open scoped NNReal

noncomputable section

universe v

/-- The literal separable, unital, nuclear, Type-I C-star algebra used in the
negative solution. -/
abbrev AntipodalCounterexampleAlgebra :=
  BaseAlgebra AntipodalCounterexampleBlock

/-- **Negative solution to STW Problem XXII.**  The literal counterexample is
unital, separable, nuclear, and Type I.  Its actual pointwise weak-star trace
simplex is nonempty and Bauer, its actual extreme-boundary subtype is compact
metrizable, the completion gauge is literally the supremum over all base
traces, and canonical extension from base traces to completion traces is
injective but not surjective.  There are no parameters or mathematical
hypotheses; Type I is asserted for an independent arbitrary Hilbert-space
universe `v`. -/
theorem negativeSolutionToProblemXXII :
    Nonempty (CStarAlgebra AntipodalCounterexampleAlgebra) ∧
      TopologicalSpace.SeparableSpace AntipodalCounterexampleAlgebra ∧
      IsNuclearCStarAlgebra AntipodalCounterexampleAlgebra ∧
      STW22.IsTypeI.{0, v} AntipodalCounterexampleAlgebra ∧
      (∀ x : AntipodalCounterexampleAlgebra,
        STW22BaseUniformTracialGauge.baseTracialTwoSize x =
          STW22Assembly.uniformTwoNorm antipodalAllTracesGauge x.1) ∧
      Set.Nonempty antipodalWeakStarTraceSimplex ∧
      IsBauerSimplex ℝ≥0 antipodalWeakStarTraceSimplex ∧
      (CompactSpace AntipodalWeakStarExtremeBoundary ∧
        MetrizableSpace AntipodalWeakStarExtremeBoundary) ∧
      Function.Injective antipodalCanonicalExtensionMap ∧
      ¬ Function.Surjective antipodalCanonicalExtensionMap :=
  negativeSolutionToProblemXXII_of_borsukUlam
    complexOddMapCommonZero_unconditional

#audit_closed_axioms negativeSolutionToProblemXXII

end

end STW22NegativeSolution
end GroupApproximation
