import GroupApproximation.Analysis.STW22AntipodalFactorialPair
import GroupApproximation.Analysis.STW22NegativeSolution
import GroupApproximation.Meta.AxiomGuard

/-!
# STW Problem XXII and the factorial-pair trace problem

`Analysis/STW22NegativeSolution` identifies the base algebra, its full trace
space, the uniform tracial completion and the injective but non-surjective
canonical extension map. This refutes printed STW Problem XXII. The companion
`Analysis/STW22UnconditionalCore` records the concrete counterexample assembly.

This file adds the proved factoriality of the designated trace pair and the
characterization of its continuous traces. These conjuncts also exhibit a
counterexample to CCEGSTW Question 1.1, whose hypothesis is a factorial
tracially complete pair. In printed XXII, factoriality is a consequence of
completion at the whole base trace space, not an additional hypothesis.
The new conjunctions assemble existing theorems about the same witness.

## Why re-typing the conjuncts is safe here

The clauses below are re-typed from the two endpoints, but they are not
re-proved.  Each package is discharged by handing over the corresponding
published theorem *unchanged*, so a clause copied inaccurately fails to
elaborate rather than landing silently: the compiler is the check on the
transcription, not the reader.  This is not a hopeful claim about the
elaborator -- a first draft of the second statement guessed four namespace
qualifications wrongly and was rejected outright.

The licence is exactly as wide as that argument and no wider.  If a future edit
makes either proof *rebuild* its clauses -- discharging them conjunct by
conjunct, or by `constructor` and a tactic block, instead of passing the
published theorem across whole -- then the correspondence stops being checked
and re-typing stops being acceptable.  Extend these conjunctions by adding
conjuncts with their own carriers, not by taking the existing ones apart.

## Why the added conjunct is content and not a formality

`IsFactorialTraciallyCompletePair X` would be worth nothing if the ambient
topology made it free, so all six fields were read rather than assumed.
`TracialState` carries the genuine pointwise weak-star topology, induced from
the product topology on `A → ℂ` (`Analysis/TracialStateWeakStarTopology.lean`),
and is Hausdorff; compactness is `compactSpace_tracialState`, which is Tychonoff
on the trace box intersected with the closed algebraic locus -- Banach--Alaoglu,
not a trivialising instance.  Closedness is an intersection of sublevel sets of
genuinely continuous functions; nonemptiness is witnessed by the canonical
extension of an actual base trace; faithfulness is forced by the coordinate norm
comparison; and the face condition is CCEGSTW's `t^{-1/2}` argument.  Each of
the six has a real carrier.
-/

namespace GroupApproximation
namespace STW22ProblemXXII

open STW22
open STW22ActualTraceSpaces
open STW22AntipodalTraceBoundary
open STW22AntipodalTraceSimplexBauer
open STW22CanonicalTraceExtension
open STW22NegativeSolution
open CStarExactness
open TopologicalSpace
open TraciallyComplete
open UniformTracialBoundedCauchyQuotient

open scoped NNReal

noncomputable section

universe v

/-- **STW Problem XXII, refuted as posed.**

The first four conjuncts answer CCEGSTW Question 1.1: the pair `(M, X)` *is* a factorial
tracially complete C-star algebra, `X` *is* exactly the set of
`‖·‖_{2,X}`-continuous traces on `M`, and the trace problem nevertheless fails
for it, in both of the forms CCEGSTW Question 1.1 is asked in.  The remaining
conjuncts are the published endpoint
`GroupApproximation.STW22NegativeSolution.negativeSolutionToProblemXXII` verbatim: the regularity
of the base algebra, the structure of its trace simplex, the gauge identity, and
the proper inclusion of trace spaces.

The second conjunct is what makes the third and fourth two readings of one
failure rather than two separate claims, and it is not `rfl`: `X` is *defined*
as the range of the canonical extension, so the content is that this range is
exactly the `‖·‖_{2,X}`-continuous traces, which is CCEGSTW Proposition 3.15.

**Two algebras appear here, and the statement moves between them.**  The first
four conjuncts are about the *completion* `M = AntipodalCompletionAlgebra`: its
designated traces `X`, the factoriality of the pair `(M, X)`, and the failure of
the trace problem.  The remaining conjuncts are about the *base* algebra
`A = AntipodalCounterexampleAlgebra`, which is `BaseAlgebra
AntipodalCounterexampleBlock` and not the completion: it is `A` that is unital,
separable, nuclear and Type I, and `A`'s trace simplex that is Bauer with
compact metrizable boundary.  Nothing here claims `M` is separable or Type I,
and a reader who quotes the conjunction should not carry those adjectives across
to `M`.  The split is the shape of the example and not an accident of assembly:
the regularity lives on `A`, and the factoriality and the trace failure live on
the pair `(M, X)`.

Type I is asserted for an arbitrary Hilbert-space universe `v`, as in the
endpoint being quoted.  There are no term binders and no mathematical
hypotheses. -/
theorem factorialNegativeSolutionToProblemXXII :
    IsFactorialTraciallyCompletePair antipodalDesignatedTraces ∧
      (∀ σ : TracialState AntipodalCompletionAlgebra,
        σ ∈ antipodalDesignatedTraces ↔
          IsUniformTwoContinuousOn antipodalDesignatedTraces σ) ∧
      ¬ AllTracesUniformTwoContinuous antipodalDesignatedTraces ∧
      ¬ DesignatedTracesAreAllTraces antipodalDesignatedTraces ∧
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
      ¬ Function.Surjective antipodalCanonicalExtensionMap := by
  obtain ⟨hfac, hmem, hcont, hall⟩ :=
    antipodalFactorialNegativeSolutionToProblemXXII
  exact ⟨hfac, hmem, hcont, hall, negativeSolutionToProblemXXII.{v}⟩

section AssemblyClauses

/-! The clauses below are transcribed from
`GroupApproximation.STW22.antipodal_stw22_trace_problem_counterexample`, so this section carries
that endpoint's own `open`s rather than the ones the printed statement above
needs. -/

open Filter PolarLiftingGeneralCStar
open UniformTracialSequenceCompletion UniformTracialTwoNullIdeal
open CuntzPedersenCoronaObstruction CuntzPedersenTraceZero STW22Assembly

/-- **The antipodal counterexample assembly, with proved factoriality.**

The second conjunct is `GroupApproximation.STW22.antipodal_stw22_trace_problem_counterexample`
verbatim, with the block-data abbreviation `B` expanded: the identification of
`ℂ1 + J` with the bounded uniform-two approximable sequences, the completion's
C-star structure, the obstruction sequence's membership in the two-null ideal
and non-membership in the null ideal, the corona trace witnessing it, and the
uniform-two discontinuous tracial state.

Those clauses are the machinery of the counterexample rather than the printed
problem's own words -- for the printed statement see
`factorialNegativeSolutionToProblemXXII` above -- but they are what the
`Analysis/STW22UnconditionalCore` endpoint asserts, and they too were asserted
without explicitly conjoining the proved factoriality. -/
theorem factorialAntipodalTraceProblemCounterexample :
    IsFactorialTraciallyCompletePair antipodalDesignatedTraces ∧
      scalarPlusJ antipodalAllTracesGauge =
        {x : BoundedCStarSequence AntipodalCounterexampleBlock |
          IsBoundedUniformTwoApproximable antipodalAllTracesGauge.toUniformTwoGauge
            (unitizedC0Sum AntipodalCounterexampleBlock) x} ∧
      Nonempty (CStarAlgebra (BoundedUniformTwoCompletion
        antipodalAllTracesGauge antipodalCoordinateNormBound
          antipodalAllTracesGauge_isCoordinateNormComparison)) ∧
      antipodalCoordinateStateBlockDataUnconditional.seq ∈
        twoNullIdeal antipodalAllTracesGauge ∧
      antipodalCoordinateStateBlockDataUnconditional.seq ∉
        nullCStarSequenceIdeal AntipodalCounterexampleBlock atTop ∧
      (∃ σ : TracialState (CStarProductCorona AntipodalCounterexampleBlock atTop),
        σ (cStarProductCoronaQuotient AntipodalCounterexampleBlock atTop
          antipodalCoordinateStateBlockDataUnconditional.seq) = 1) ∧
      cStarProductCoronaQuotient AntipodalCounterexampleBlock atTop
          antipodalCoordinateStateBlockDataUnconditional.seq ∉
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
        ¬ Tendsto (fun N ↦ σ (x N)) atTop (nhds 0)) :=
  ⟨antipodal_isFactorialTraciallyCompletePair,
    antipodal_stw22_trace_problem_counterexample⟩

end AssemblyClauses

#audit_closed_axioms factorialNegativeSolutionToProblemXXII
#audit_closed_axioms factorialAntipodalTraceProblemCounterexample

end

end STW22ProblemXXII
end GroupApproximation
