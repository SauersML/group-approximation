import GroupApproximation.Kazhdan.FoxRelationSequence
import GroupApproximation.Meta.AxiomGuard

/-!
# The Fox complex of a presentation is exact in low degrees

Step A1 of the torsion-freeness route (a1) for the Kazhdan hyperbolic group: for every
presentation `⟨X | rel⟩` by signed words, the integral Fox complex

`ℤG^ρ →∂₂ ℤG^X →∂₁ ℤG →ε ℤ → 0`

on the free modules `FreeZG` of `Algebra/FreeResolutionPrimeOrder.lean` is exact at `ℤ`, at
`ℤG` and at `ℤG^X`.  Stated as one closed proposition for the consumer (asphericity makes
`∂₂` injective, and the resolution then feeds `isPowerTorsionFree_of_resolution`).
-/

namespace GroupApproximation.FoxComplex

open FreeResolutionPrimeOrder FoxBoundary PresentedGroupRelatorReplay

universe v w

/-- **Low-degree exactness of the Fox complex**, for every signed-word presentation. -/
def FoxComplexExactEveryPresentation : Prop :=
  ∀ (X : Type v) (ρ : Type w) (rel : ρ → SignedWord X),
    Function.Surjective (augZ : FreeZG (Presented rel) Unit →+ ℤ) ∧
    (foxD₁ (PresentedGroup.of : X → Presented rel)).range =
      (augZ : FreeZG (Presented rel) Unit →+ ℤ).ker ∧
    (foxD₁ (PresentedGroup.of : X → Presented rel)).ker =
      (foxD₂ (PresentedGroup.of : X → Presented rel) rel).range

/-- **Closed endpoint**: the Fox complex of every presentation is exact at `ℤ`, `ℤG` and
`ℤG^X`. -/
theorem foxComplexExact_everyPresentation : FoxComplexExactEveryPresentation.{v, w} :=
  fun _ _ rel ↦ ⟨augZ_surjective, range_foxD₁_eq_ker_augZ _ (presented_generates rel),
    ker_foxD₁_eq_range_foxD₂ rel⟩

end GroupApproximation.FoxComplex

/-! ### Axiom audit -/

#audit_closed_axioms GroupApproximation.FoxComplex.foxComplexExact_everyPresentation
