import GroupApproximation.Analysis.MaximalGroupCStarTrace

/-!
# The maximal regular representation along a group homomorphism
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open ReducedGroupCStarTrace

noncomputable section

/-- The maximal representation obtained from a group map and the target's left
regular representation. -/
def maximalToReducedAlong {H K : Type} [Group H] [Group K]
    (i : H →* K) : MaximalGroupCStar H →⋆ₐ[ℂ] ReducedGroupCStar K :=
  maximalGroupCStarLift H ((reducedLeftRegularUnitaryHom K).comp i)

@[simp] theorem maximalToReducedAlong_generator {H K : Type} [Group H]
    [Group K] (i : H →* K) (h : H) :
    maximalToReducedAlong i (maximalGroupCStarGenerator H h) =
      reducedLeftRegular K (i h) :=
  maximalGroupCStarLift_generator H
    ((reducedLeftRegularUnitaryHom K).comp i) h

end


end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
