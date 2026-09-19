import GroupApproximation.Analysis.CStarNuclearProduct

/-!
# Completely positive contractive retracts preserve nuclearity

This is the direct CPAP permanence lemma used for the antipodal fixed-point
blocks.  It is proved by composing the finite-dimensional approximations with
the inclusion and retraction.
-/

namespace GroupApproximation
namespace CStarExactness

noncomputable section

universe u v

/-- A completely positive contractive retract of a nuclear C-star algebra is
nuclear. -/
theorem IsNuclearCStarAlgebra.of_cpContractiveRetract
    {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (ι : A →⋆ₙₐ[ℂ] B) (retract : B →ₗ[ℂ] A)
    (hretractCP : IsCompletelyPositive retract)
    (hretractContractive : ∀ b, ‖retract b‖ ≤ ‖b‖)
    (hretractInclude : ∀ a, retract (ι a) = a)
    (hB : IsNuclearCStarAlgebra B) :
    IsNuclearCStarAlgebra A := by
  classical
  intro F ε hε
  obtain ⟨D, α, β, hα, hβ, hαc, hβc, happ⟩ :=
    hB (F.image ι) ε hε
  let down : A →ₗ[ℂ] D := α.comp (ι : A →ₗ[ℂ] B)
  let up : D →ₗ[ℂ] A := retract.comp β
  refine ⟨D, down, up,
    hα.comp (isCompletelyPositive_of_starAlgHom ι),
    hretractCP.comp hβ, ?_, ?_, ?_⟩
  · intro a
    change ‖α (ι a)‖ ≤ ‖a‖
    exact (hαc (ι a)).trans (NonUnitalStarAlgHom.norm_apply_le ι a)
  · intro d
    change ‖retract (β d)‖ ≤ ‖d‖
    exact (hretractContractive (β d)).trans (hβc d)
  · intro a ha
    change ‖retract (β (α (ι a))) - a‖ ≤ ε
    calc
      ‖retract (β (α (ι a))) - a‖ =
          ‖retract (β (α (ι a)) - ι a)‖ := by
            rw [map_sub, hretractInclude]
      _ ≤ ‖β (α (ι a)) - ι a‖ :=
        hretractContractive _
      _ ≤ ε := happ (ι a) (Finset.mem_image_of_mem ι ha)

end

end CStarExactness
end GroupApproximation
