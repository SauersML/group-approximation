import GroupApproximation.Manuscript.MFRecognition.HNNTraceBaseTrace

/-!
# Factorization of the HNN base representation through `C*_r(G)`
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open ReducedGroupCStarTrace
open GroupApproximation.HNNTrace

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The maximal-to-reduced map kills the kernel of the maximal-to-base map. -/
theorem maximalToReduced_eq_zero_of_maximalToBase_eq_zero
    (data : CoronaConjugator G S T phi A X) (a : MaximalGroupCStar G)
    (ha : maximalToBase data a = 0) :
    maximalGroupCStarToReduced G a = 0 := by
  apply ((canonicalFaithfulTracialState G).map_star_mul_self_eq_zero_iff _).mp
  have htrace := congrArg (fun f : MaximalGroupCStar G →L[ℂ] ℂ ↦
      f (star a * a)) (baseTrace_comp_maximalToBase data)
  change baseTrace data (maximalToBase data (star a * a)) =
      canonicalCoefficientAtOne G
        (maximalGroupCStarToReduced G (star a * a)) at htrace
  rw [map_mul, map_star, ha, star_zero, zero_mul, TracialState.map_zero,
    map_mul, map_star] at htrace
  exact htrace.symm

/-- The printed homomorphism `π : D → C*_r(G)`. -/
def reducedFactorisation (data : CoronaConjugator G S T phi A X) :
    baseAlgebra data →⋆ₐ[ℂ] ReducedGroupCStar G :=
  descendStarAlgHom (maximalToBase data) (maximalGroupCStarToReduced G)
    (maximalToBase_surjective data)
    (maximalToReduced_eq_zero_of_maximalToBase_eq_zero data)

@[simp] theorem reducedFactorisation_apply
    (data : CoronaConjugator G S T phi A X) (g : G) :
    reducedFactorisation data
        (((baseUnitaryHom data g : unitary (baseAlgebra data)) :
          baseAlgebra data)) = reducedLeftRegular G g := by
  rw [← maximalToBase_generator data g]
  change descendStarAlgHom (maximalToBase data) (maximalGroupCStarToReduced G)
      (maximalToBase_surjective data)
      (maximalToReduced_eq_zero_of_maximalToBase_eq_zero data)
      (maximalToBase data (maximalGroupCStarGenerator G g)) = _
  calc
    _ = maximalGroupCStarToReduced G (maximalGroupCStarGenerator G g) := by
      apply descendStarAlgHom_comp_apply
    _ = reducedLeftRegular G g := maximalGroupCStarToReduced_generator G g

end


end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
