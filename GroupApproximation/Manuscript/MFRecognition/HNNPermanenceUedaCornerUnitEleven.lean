import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaAmalgamCommonImage
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaElevenLeftInclusion
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaElevenRightInclusion

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The printed identity `e₂₂ = f₂₂`, which is `ι_A(0, 1_D) = ι_B(0, 1_D)`. -/
theorem matrixUnitLeft_one_one_eq_right
    (data : CoronaConjugator G S T phi A X) :
    matrixUnitLeft data 1 1 = matrixUnitRight data 1 1 := by
  have hcommon := amalgam_commonImage data
    ((0 : sourceEdgeAlgebra data), (1 : targetEdgeAlgebra data))
  exact (amalgamLeftInclusion_zero_one_eq_matrixUnitLeft data).symm.trans
    (hcommon.trans
      (amalgamRightInclusion_zero_one_eq_matrixUnitRight data))

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
