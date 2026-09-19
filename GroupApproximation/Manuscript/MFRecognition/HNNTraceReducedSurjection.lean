import GroupApproximation.Analysis.MaximalGroupCStarTrace
import GroupApproximation.Analysis.ReducedGroupCStarSpan
import GroupApproximation.Analysis.HNNTraceStarAlgHomDescent

/-!
# Surjectivity of the maximal-to-reduced group C-star map
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open ReducedGroupCStarTrace
open GroupApproximation.HNNTrace

noncomputable section

local instance reducedSurjectionMaximalGroupCStarNontrivial
    (H : Type) [Group H] : Nontrivial (MaximalGroupCStar H) := by
  refine ⟨1, 0, fun h ↦ ?_⟩
  have heval := congrArg (maximalGroupCStarEval H
    (CStarUnitaryRepresentation.reduced H)) h
  rw [map_one, map_zero] at heval
  exact one_ne_zero heval

/-- The canonical maximal-to-reduced map is onto. -/
theorem maximalGroupCStarToReduced_surjective (H : Type) [Group H] :
    Function.Surjective (maximalGroupCStarToReduced H) := by
  have hdense : DenseRange (maximalGroupCStarToReduced H) := by
    change Dense (Set.range (maximalGroupCStarToReduced H))
    rw [Metric.dense_iff]
    intro y ε hε
    obtain ⟨n, c, γ, happ⟩ := exists_translationSum_approx H y.property hε
    let a : MaximalGroupCStar H :=
      ∑ i : Fin n, c i • maximalGroupCStarGenerator H (γ i)
    refine ⟨maximalGroupCStarToReduced H a, ?_, ⟨a, rfl⟩⟩
    rw [Metric.mem_ball, dist_comm, dist_eq_norm]
    change ‖(y : GroupHilbert H →L[ℂ] GroupHilbert H) -
      ((maximalGroupCStarToReduced H a : ReducedGroupCStar H) :
        GroupHilbert H →L[ℂ] GroupHilbert H)‖ < ε
    simpa [a, map_sum, map_smul, maximalGroupCStarToReduced_generator,
      reducedLeftRegular] using happ
  rw [← Set.range_eq_univ]
  calc
    Set.range (maximalGroupCStarToReduced H) =
        closure (Set.range (maximalGroupCStarToReduced H)) :=
      (isClosed_range_starAlgHom (maximalGroupCStarToReduced H)).closure_eq.symm
    _ = Set.univ := hdense.closure_eq

end


end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
