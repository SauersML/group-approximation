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

/-- The family of nonempty tracial-state spaces of the antipodal blocks, as a
single `∀ n, …` instance.

Every consumer below takes this as an instance-implicit binder, and synthesis
cannot supply it here: `AntipodalCounterexampleBlock` abbreviates
`RealProjectiveBlock`, whose instance search is pathological in this repository
(a `Zero` search emitting ~23k trace lines before dying inside `Grind`
instances, measured 2026-08-31).  Nine declarations in this file failed to
elaborate for that reason alone, and Lean poisons a failed declaration with
`sorryAx`, so all four `#audit_closed_axioms` gates at the end of the file
reported `sorryAx` with no `sorry` anywhere in the source.

Naming the family directly is the structural fix — the same one
`STW22AntipodalBlockData.antipodalAllTracesGauge` already uses four lines below
the underlying instance, where it `@`-applies `allTracesTracialTwoGauge` and
passes `(fun n ↦ nonemptyTracialState_antipodalCounterexampleBlock n)` by hand
rather than letting the binder be synthesized.  The campaign rule is that a
timeout gets a structural fix, never a `maxHeartbeats` bump. -/
instance instNonemptyTracialStateAntipodalFamily :
    ∀ n, Nonempty (TracialState (AntipodalCounterexampleBlock n)) :=
  fun n ↦ nonemptyTracialState_antipodalCounterexampleBlock n

/-- The canonical extension map `T(A) → T(M)` of the antipodal counterexample,
with every instance argument supplied by hand.

Registering the family above is necessary but not sufficient, and a diagnostic
build says so: with the six standalone goals
`(∀ n,) CStarAlgebra / Nontrivial / Nonempty (TracialState …)` all discharged by
`inferInstance` in the same context, the *application*
`canonicalExtension antipodalAllTracesGauge_isCoordinateNormComparison` still
fails on the `Nonempty` binder, in the statement as well as in the proof, while
the `@`-applied form below elaborates.  The reason is not findability: the
elaborator reaches that binder before `D` is determined, because the only
argument that would determine it is the comparison datum, whose own type is
stated through the gauge abbreviation `G D`.  A goal `∀ n, Nonempty (TracialState
(?D n))` has no solution however many instances are registered.

Being an `abbrev`, this *is* `canonicalExtension …` rather than merely equal to
it, so nothing downstream is weakened by naming it. -/
noncomputable abbrev antipodalCanonicalExtensionMap :=
  @canonicalExtension AntipodalCounterexampleBlock inferInstance inferInstance
    instNonemptyTracialStateAntipodalFamily antipodalCoordinateNormBound
    antipodalAllTracesGauge_isCoordinateNormComparison

/-- The sequence-model gauge used throughout is exactly the supremum of the
two-norms coming from all bundled tracial states of the actual base algebra.
No topological input is involved. -/
theorem antipodalBaseTracialTwoSize_eq_completionGauge
    (x : BaseAlgebra AntipodalCounterexampleBlock) :
    STW22BaseUniformTracialGauge.baseTracialTwoSize x =
      STW22Assembly.uniformTwoNorm antipodalAllTracesGauge x.1 :=
  @STW22BaseUniformTracialGauge.baseTracialTwoSize_eq_uniformTwoNorm_allTraces
    AntipodalCounterexampleBlock inferInstance inferInstance
    instNonemptyTracialStateAntipodalFamily x

/-- The canonical map from the actual base trace space to the actual bounded
uniform-two completion trace space is injective.  This half of the proper
inclusion needs no topological input at all: it is inverted by restriction. -/
theorem antipodalCanonicalExtension_injective :
    Function.Injective antipodalCanonicalExtensionMap :=
  @canonicalExtension_injective AntipodalCounterexampleBlock inferInstance
    inferInstance instNonemptyTracialStateAntipodalFamily
    antipodalCoordinateNormBound
    antipodalAllTracesGauge_isCoordinateNormComparison

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
    ¬ Function.Surjective antipodalCanonicalExtensionMap :=
  @canonicalExtension_not_surjective_of_not_every AntipodalCounterexampleBlock
    inferInstance inferInstance instNonemptyTracialStateAntipodalFamily
    antipodalCoordinateNormBound
    antipodalAllTracesGauge_isCoordinateNormComparison
    (not_everyAntipodalCompletionTraceIsContinuousExtension_of_borsukUlam hBU)

/-- The literal trace-space proper inclusion `T(A) ⊊ T(M)`, with the
topological input explicit. -/
theorem antipodal_trace_space_strict_inclusion_of_borsukUlam
    (hBU : ComplexOddMapCommonZero) :
    Function.Injective antipodalCanonicalExtensionMap ∧
    ¬ Function.Surjective antipodalCanonicalExtensionMap :=
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
      Function.Injective antipodalCanonicalExtensionMap ∧
      ¬ Function.Surjective antipodalCanonicalExtensionMap :=
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
