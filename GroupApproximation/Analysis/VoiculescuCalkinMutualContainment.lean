import GroupApproximation.Analysis.VoiculescuAbsorption

/-!
# The honest Calkin consequence of isometric absorption

`AbsorptionContainmentStatement` is weaker than the usual unitary form of
Voiculescu absorption: it produces an isometry `v` satisfying

    `sigma(a) v - v tau(a) ∈ K(H)`.

Applying it in both directions therefore produces two isometric
intertwiners.  It does not by itself produce a unitary.  This module records
and proves that strongest immediate consequence, so the remaining V5 seam is
not hidden behind the phrase "apply absorption twice and compose".

The distinction is load-bearing in the Calkin algebra: an isometry need not be
unitary.  Turning the pair below into the unitary demanded by
`CalkinUniquenessStatement` requires the full unitary absorption argument (or
an equivalent infinite-sum/intertwining construction), not ring algebra on the
two isometries.
-/

namespace GroupApproximation
namespace ShulmanFill

noncomputable section

/-- **Mutual containment modulo the compacts.**  Each representation embeds
isometrically into the other modulo compact intertwining defects.

This is the strongest formal consequence of
`AbsorptionContainmentStatement` obtained by applying it in both directions;
unlike `CalkinUniquenessStatement`, it deliberately makes no claim that either
isometry is unitary. -/
def CalkinMutualContainmentStatement : Prop :=
  ∀ (C : Type) [CStarAlgebra C] [TopologicalSpace.SeparableSpace C]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [TopologicalSpace.SeparableSpace H]
    (sigma tau : C →⋆ₐ[ℂ] (H →L[ℂ] H)),
      (∀ a : C, IsCompactOperator (sigma a) → a = 0) →
      (∀ a : C, IsCompactOperator (tau a) → a = 0) →
        ∃ v w : H →L[ℂ] H,
          ContinuousLinearMap.adjoint v ∘L v = 1 ∧
          ContinuousLinearMap.adjoint w ∘L w = 1 ∧
          ∀ a : C,
            IsCompactOperator (sigma a ∘L v - v ∘L tau a) ∧
            IsCompactOperator (tau a ∘L w - w ∘L sigma a)

/-- **The exact twice-applied absorption conclusion.** -/
theorem calkinMutualContainment_of_absorption
    (h : AbsorptionContainmentStatement) :
    CalkinMutualContainmentStatement := by
  intro C _instC _sepC H _ _ _ _ sigma tau hsigma htau
  obtain ⟨v, hv, hvint⟩ := h C H H sigma tau hsigma
  obtain ⟨w, hw, hwint⟩ := h C H H tau sigma htau
  exact ⟨v, w, hv, hw, fun a ↦ ⟨hvint a, hwint a⟩⟩

end

end ShulmanFill
end GroupApproximation
