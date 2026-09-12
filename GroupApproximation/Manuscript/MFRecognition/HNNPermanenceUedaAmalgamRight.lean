import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaAmalgamLeft

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The canonical copy of `A₂ = M₂(B₀)` in `P`. -/
def amalgamRight (data : CoronaConjugator G S T phi A X) :
    matrixEdgeAlgebra data →⋆ₐ[ℂ] amalgam data := by
  letI : Nonempty (CStarAmalgamRepresentation
      (amalgamLeftInclusion data) (amalgamRightInclusion data)) :=
    ⟨coronaAmalgamRepresentation data⟩
  exact universalCStarAmalgamRight
    (amalgamLeftInclusion data) (amalgamRightInclusion data)

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
