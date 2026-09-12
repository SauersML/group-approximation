import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaMatrixUnitLeft

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The first half of `e = ι_A(1_D, 0) = ι_B(1_D, 0)`. -/
theorem cornerUnit_eq_matrixUnitLeft
    (data : CoronaConjugator G S T phi A X) :
    cornerUnit data = matrixUnitLeft data 0 0 :=
  rfl

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
