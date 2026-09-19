import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaEvaluatedComposite

/-! # The faithful Ueda corner map -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- Printed: *"the induced map is injective"*.  With Step 1 taken as a named
input this is the input's own third clause; the coordinate argument that would
prove it outright is blocked by the universe gap recorded on
`UedaCornerMapStatement`. -/
theorem uedaCornerMap_injective (hUeda : UedaCornerMapStatement)
    (data : CoronaConjugator G S T phi A X) :
    Function.Injective (uedaCornerMap hUeda data) :=
  (hUeda data).choose_spec.2.2

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
