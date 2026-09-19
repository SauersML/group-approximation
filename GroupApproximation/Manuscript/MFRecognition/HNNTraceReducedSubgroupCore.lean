import GroupApproximation.Analysis.ReducedGroupCStarMFObstruction
import GroupApproximation.Manuscript.MFRecognition.HNNTraceReducedAlongTrace
import GroupApproximation.Manuscript.MFRecognition.HNNTraceReducedSurjection

/-!
# Kernel descent for reduced group C-star maps
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open ReducedGroupCStarTrace
open GroupApproximation.HNNTrace

noncomputable section

theorem maximalToReducedAlong_eq_zero_of_toReduced_eq_zero
    {H K : Type} [Group H] [Group K] (i : H →* K)
    (hi : Function.Injective i) (a : MaximalGroupCStar H)
    (ha : maximalGroupCStarToReduced H a = 0) :
    maximalToReducedAlong i a = 0 := by
  apply ((canonicalFaithfulTracialState K).map_star_mul_self_eq_zero_iff _).mp
  have htrace := congrArg (fun f : MaximalGroupCStar H →L[ℂ] ℂ ↦
      f (star a * a)) (maximalToReducedAlong_trace i hi)
  change canonicalCoefficientAtOne K
      (maximalToReducedAlong i (star a * a)) =
    canonicalCoefficientAtOne H
      (maximalGroupCStarToReduced H (star a * a)) at htrace
  have hleft : maximalToReducedAlong i (star a * a) =
      star (maximalToReducedAlong i a) * maximalToReducedAlong i a := by
    rw [map_mul, map_star]
  have hright : maximalGroupCStarToReduced H (star a * a) = 0 := by
    rw [map_mul, map_star, ha, star_zero, zero_mul]
  rw [hleft, hright, map_zero] at htrace
  exact htrace

/-- Every injective group homomorphism induces the corresponding homomorphism
between reduced group C-star algebras. -/
def reducedGroupCStarMapOfInjective {H K : Type} [Group H] [Group K]
    (i : H →* K) (hi : Function.Injective i) :
    ReducedGroupCStar H →⋆ₐ[ℂ] ReducedGroupCStar K :=
  descendStarAlgHom (maximalGroupCStarToReduced H) (maximalToReducedAlong i)
    (maximalGroupCStarToReduced_surjective H)
    (maximalToReducedAlong_eq_zero_of_toReduced_eq_zero i hi)

@[simp] theorem reducedGroupCStarMapOfInjective_apply {H K : Type} [Group H]
    [Group K] (i : H →* K) (hi : Function.Injective i) (h : H) :
    reducedGroupCStarMapOfInjective i hi (reducedLeftRegular H h) =
      reducedLeftRegular K (i h) := by
  rw [← maximalGroupCStarToReduced_generator H h]
  change descendStarAlgHom (maximalGroupCStarToReduced H)
      (maximalToReducedAlong i) (maximalGroupCStarToReduced_surjective H)
      (maximalToReducedAlong_eq_zero_of_toReduced_eq_zero i hi)
      (maximalGroupCStarToReduced H (maximalGroupCStarGenerator H h)) = _
  calc
    _ = maximalToReducedAlong i (maximalGroupCStarGenerator H h) := by
      apply descendStarAlgHom_comp_apply
    _ = reducedLeftRegular K (i h) := maximalToReducedAlong_generator i h

end


end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
