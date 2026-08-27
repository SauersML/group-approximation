import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaAmalgamPackage

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

variable (data : CoronaConjugator G S T phi A X)

/-- The canonical copy of `A₁ = M₂(D)` in `P`. -/
def amalgamLeft :
    matrixBaseAlgebra data →⋆ₐ[ℂ] amalgam data :=
  @universalCStarAmalgamLeft
    (edgeSumAlgebra data) (matrixBaseAlgebra data) (matrixEdgeAlgebra data)
    inferInstance inferInstance inferInstance
    (amalgamLeftInclusion data) (amalgamRightInclusion data)
    ⟨coronaAmalgamRepresentation data⟩

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
