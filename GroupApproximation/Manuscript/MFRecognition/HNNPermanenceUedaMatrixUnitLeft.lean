import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerUnit

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The printed matrix units `e_ij` of `A₁`, transported to `P`. -/
def matrixUnitLeft (data : CoronaConjugator G S T phi A X) (i j : Fin 2) :
    amalgam data :=
  amalgamLeft data (cStarMatrixUnitTwo i j (1 : baseAlgebra data))

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
