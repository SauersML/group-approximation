import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerUnitLeftCommon
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaAmalgamCommonImage

/-! # The corner unit as a right-factor common image -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem cornerUnit_eq_amalgamRightInclusion
    (data : CoronaConjugator G S T phi A X) :
    cornerUnit data =
      amalgamRight data (amalgamRightInclusion data
        ((1 : sourceEdgeAlgebra data), (0 : targetEdgeAlgebra data))) := by
  exact (cornerUnit_eq_amalgamLeftInclusion data).trans
    (amalgam_commonImage data
      ((1 : sourceEdgeAlgebra data), (0 : targetEdgeAlgebra data)))

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
