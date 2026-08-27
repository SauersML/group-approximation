import GroupApproximation.Analysis.ReducedGroupCStarMFObstruction
import GroupApproximation.Manuscript.MFRecognition.HNNTraceReducedAlongMap

/-!
# The canonical trace of an injective regular representation
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open ReducedGroupCStarTrace

noncomputable section

theorem maximalToReducedAlong_trace {H K : Type} [Group H] [Group K]
    (i : H →* K) (hi : Function.Injective i) :
    compContinuousFunctional H (maximalToReducedAlong i)
        (canonicalCoefficientAtOne K) = canonicalMaximalTrace H := by
  apply canonicalMaximalTrace_eq_of_generator H
  · change canonicalCoefficientAtOne K
      (maximalToReducedAlong i (maximalGroupCStarGenerator H 1)) = 1
    rw [maximalToReducedAlong_generator, map_one, reducedLeftRegular_one]
    exact canonicalCoefficientAtOne_one K
  · intro h hh
    change canonicalCoefficientAtOne K
      (maximalToReducedAlong i (maximalGroupCStarGenerator H h)) = 0
    rw [maximalToReducedAlong_generator]
    exact canonicalCoefficientAtOne_reducedLeftRegular_of_ne_one K
      (fun hih ↦ hh (hi (hih.trans (map_one i).symm)))

end


end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
