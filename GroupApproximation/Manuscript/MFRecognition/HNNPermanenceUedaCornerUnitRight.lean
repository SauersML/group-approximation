import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerUnitCommonImage
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerUnitRightInclusion

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The second half of `e = ι_A(1_D, 0) = ι_B(1_D, 0)`. -/
theorem cornerUnit_eq_matrixUnitRight
    (data : CoronaConjugator G S T phi A X) :
    cornerUnit data = matrixUnitRight data 0 0 :=
  (cornerUnit_eq_amalgamRightInclusion data).trans
    (amalgamRightInclusion_one_zero_eq_matrixUnitRight data)

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
