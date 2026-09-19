import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaAmalgamRight

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The printed matrix units `f_ij` of `A₂`, transported to `P`. -/
def matrixUnitRight (data : CoronaConjugator G S T phi A X) (i j : Fin 2) :
    amalgam data :=
  amalgamRight data (cStarMatrixUnitTwo i j (1 : sourceEdgeAlgebra data))

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
