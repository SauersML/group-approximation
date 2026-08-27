import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaEvaluatedCompatibilityApply

/-! # Compatibility of the evaluated Ueda factor maps -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

variable (data : CoronaConjugator G S T phi A X)

theorem evaluatedFactor_compatible (R : HNNCoordinate data) :
    (evaluatedFactorLeft data R).comp (amalgamLeftInclusion data) =
      (evaluatedFactorRight data R).comp (amalgamRightInclusion data) := by
  apply StarAlgHom.ext
  intro c
  exact (evaluatedFactor_compatible_apply data R c).symm

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
