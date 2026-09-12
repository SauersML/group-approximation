import GroupApproximation.GGT.KazhdanHypGirthEightStarProducer

/-!
# Universal hyperbolicity assembly

The theorem below is the exact final consumer: a source for the fully built
successive-star record gives `GirthEightHyperbolicity` for every finite table
and every checked girth parameter.  The source is kept as one named input
because the clean vk API does not prove the five global producers by itself.
No extra geometric fact is introduced after the source is supplied.
-/

namespace GroupApproximation
namespace GGT
namespace KazhdanHypGirthEightUnconditional

open GroupApproximation.GGT.GirthEightVKInterface
open GroupApproximation.GGT.KazhdanHypGirthEightStarProducer
open GroupApproximation.KazhdanHyp
open GroupApproximation.WordMetric

/-! ## Exact universal source and assembly -/

/-- For every finite triangle table and every checked girth parameter, the
source supplies the successive-star record required by the slim-triangle
consumer at every geodesic configuration. -/
def SuccessiveStarSource : Prop :=
  ∀ (Generator TriangleIndex : Type)
    (_ : Fintype Generator) (_ : DecidableEq Generator)
    (_ : Nonempty Generator) (_ : Fintype TriangleIndex)
    (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (d delta : ℕ),
    GirthEightChecks T d →
    ∀ (x y z p : TriangularHodgeLayer.Presented T),
      Hyperbolic.IsBetween
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) x p y →
      (∀ q : TriangularHodgeLayer.Presented T,
        Hyperbolic.IsBetween
          (↑(GirthEightSlim.presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) x q z →
        delta < wordDist
          (↑(GirthEightSlim.presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) p q) →
      (∀ q : TriangularHodgeLayer.Presented T,
        Hyperbolic.IsBetween
          (↑(GirthEightSlim.presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) z q y →
        delta < wordDist
          (↑(GirthEightSlim.presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) p q) →
      ∃ S : SuccessiveStarLayers T, S.diagram.Reduced

/-- The exact universal `GirthEightHyperbolicity` conclusion. -/
theorem girthEightHyperbolicity_unconditional_of_source
    (hsource : SuccessiveStarSource) :
    GirthEightHyperbolicity := by
  intro Generator TriangleIndex fg dg ng ft dt T d hchecks
  apply GirthEightSlim.presented_isHyperbolicGroup_of_girthEight_layer_construction
    hchecks
  intro x y z p hp hfarXZ hfarZY
  obtain ⟨S, _hred⟩ := hsource Generator TriangleIndex fg dg ng ft dt T d 1
    hchecks x y z p hp hfarXZ hfarZY
  exact ⟨S.diagram, S.localData, S.depth, S.scale, S.loss, S.perimeter,
    S.layer, S.boundary_bound, S.layer_disjoint, S.layer_covers,
    S.depth_too_large⟩

end KazhdanHypGirthEightUnconditional
end GGT
end GroupApproximation
