import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerUnitLeftInclusion

/-! # The corner unit as the left-factor image of `(1,0)` -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem cornerUnit_eq_amalgamLeftInclusion
    (data : CoronaConjugator G S T phi A X) :
    cornerUnit data =
      amalgamLeft data (amalgamLeftInclusion data
        ((1 : sourceEdgeAlgebra data), (0 : targetEdgeAlgebra data))) := by
  exact (cornerUnit_eq_matrixUnitLeft data).trans
    (amalgamLeftInclusion_one_zero_eq_matrixUnitLeft data).symm

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
