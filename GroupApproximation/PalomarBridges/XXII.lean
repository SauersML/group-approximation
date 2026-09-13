/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.Analysis.STW22ProblemXXIIFactorialEndpoint

/-!
# Bridges for the Palomar statement of STW Problem XXII

`Palomar/STWProblemXXIISolution.lean` answers Problem XXII of Schafhauser, Tikuisis and White
with the antipodal pair `(AntipodalCompletionAlgebra, antipodalDesignatedTraces)` of
`Analysis/STW22AntipodalFactorialPair`. Its statement presents that pair as the uniform tracial
completion of the base algebra `AntipodalCounterexampleAlgebra`: restriction along the inclusion
`antipodalBaseToCompletion` is a bijection from the designated traces onto the tracial states of
the base algebra, and the image of the base algebra is `‖·‖_{2,X}`-dense. This module proves those
facts about the development's objects, together with separability of the base algebra.

* `antipodalCanonicalExtensionMap_baseToCompletion`: a canonical extension restricts to the base
  trace it extends.
* `antipodal_existsUnique_restrict`: every tracial state of the base algebra has exactly one
  designated extension, its canonical extension.
* `antipodal_dense`: every element of the completion is a `‖·‖_{2,X}`-limit of images of base
  elements, namely of a chosen bounded approximating sequence.
* `antipodal_separableSpace`: the base algebra is separable.

The development's lemmas carry the family `∀ n, Nonempty (TracialState (D n))` as an instance
binder that elaboration reaches before `D` is known, so they are applied here with every instance
argument supplied by hand, as in `Analysis/STW22ConditionalNegativeSolution`.
-/

namespace GroupApproximation
namespace PalomarBridges
namespace XXII

open Filter
open UniformTracialBoundedCauchyQuotient STW22ActualTraceSpaces STW22CanonicalTraceExtension
open TraciallyComplete STW22 STW22FactorialCore STW22NegativeSolution

/-- The inclusion of the base algebra into its uniform tracial completion. -/
noncomputable abbrev antipodalBaseToCompletion :
    AntipodalCounterexampleAlgebra →⋆ₐ[ℂ] AntipodalCompletionAlgebra :=
  baseToCompletion antipodalAllTracesGauge antipodalAllTracesGauge_isCoordinateNormComparison

/-- A canonical extension restricts to the base trace it extends. -/
theorem antipodalCanonicalExtensionMap_baseToCompletion
    (τ : TracialState AntipodalCounterexampleAlgebra) (a : AntipodalCounterexampleAlgebra) :
    antipodalCanonicalExtensionMap τ (antipodalBaseToCompletion a) = τ a :=
  @canonicalExtension_baseToCompletion_apply AntipodalCounterexampleBlock inferInstance
    inferInstance instNonemptyTracialStateAntipodalFamily antipodalCoordinateNormBound
    antipodalAllTracesGauge_isCoordinateNormComparison τ a

/-- Every tracial state of the base algebra has exactly one designated extension to the
completion. -/
theorem antipodal_existsUnique_restrict (τ : TracialState AntipodalCounterexampleAlgebra) :
    ∃! σ : TracialState AntipodalCompletionAlgebra,
      σ ∈ antipodalDesignatedTraces ∧ ∀ a, σ (antipodalBaseToCompletion a) = τ a := by
  refine ⟨antipodalCanonicalExtensionMap τ,
    ⟨Set.mem_range_self τ, antipodalCanonicalExtensionMap_baseToCompletion τ⟩, ?_⟩
  rintro σ ⟨⟨τ', rfl⟩, h⟩
  have hτ : τ' = τ := tracialState_ext fun a ↦
    (antipodalCanonicalExtensionMap_baseToCompletion τ' a).symm.trans (h a)
  rw [hτ]

/-- The image of the base algebra is `‖·‖_{2,X}`-dense in the completion. -/
theorem antipodal_dense (m : AntipodalCompletionAlgebra) :
    ∃ x : ℕ → AntipodalCounterexampleAlgebra,
      Tendsto (fun k ↦ uniformTwoNormOn antipodalDesignatedTraces
        (m - antipodalBaseToCompletion (x k))) atTop (nhds 0) := by
  rw [antipodalDesignatedTraces_eq_gauge]
  obtain ⟨s, -, hs⟩ := @chosenApproximation AntipodalCounterexampleBlock inferInstance
    inferInstance instNonemptyTracialStateAntipodalFamily
    (realize antipodalAllTracesGauge antipodalAllTracesGauge_isCoordinateNormComparison m)
  refine ⟨s, hs.congr fun k ↦ ?_⟩
  exact ((@completionGauge_sub_baseToCompletion AntipodalCounterexampleBlock inferInstance
    inferInstance instNonemptyTracialStateAntipodalFamily antipodalCoordinateNormBound
    antipodalAllTracesGauge_isCoordinateNormComparison m (s k)).symm.trans
      (@uniformTwoNormOn_designatedTraces AntipodalCounterexampleBlock inferInstance
        inferInstance instNonemptyTracialStateAntipodalFamily antipodalCoordinateNormBound
        antipodalAllTracesGauge_isCoordinateNormComparison _).symm)

/-- The base algebra is separable. -/
theorem antipodal_separableSpace :
    TopologicalSpace.SeparableSpace AntipodalCounterexampleAlgebra :=
  (STW22ProblemXXII.factorialNegativeSolutionToProblemXXII.{0}).2.2.2.2.2.1

end XXII
end PalomarBridges
end GroupApproximation
