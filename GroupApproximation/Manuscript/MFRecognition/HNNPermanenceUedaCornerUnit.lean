import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaAmalgamLeft

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-! ## The projection `e` and the matrix units -/

/-- Printed: *"the projection `e = ι_A(1_D, 0) = ι_B(1_D, 0)`"*. -/
def cornerUnit (data : CoronaConjugator G S T phi A X) : amalgam data :=
  amalgamLeft data (cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data))

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
