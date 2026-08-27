import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaAmalgamPackageType

/-!
# The bundled full amalgam used by Ueda's corner model

Bundling the carrier together with its C-star structure keeps downstream
typeclass search from unfolding the universe-sized universal product.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- Printed: *"let `P = A₁ *_C A₂` be the full amalgamated free product"*. -/
def amalgam (data : CoronaConjugator G S T phi A X) :
    PackagedCStarAlgebra := by
  letI : Nonempty (CStarAmalgamRepresentation
      (amalgamLeftInclusion data) (amalgamRightInclusion data)) :=
    ⟨coronaAmalgamRepresentation data⟩
  exact
    { carrier := UniversalCStarAmalgam
        (amalgamLeftInclusion data) (amalgamRightInclusion data)
      instCStarAlgebra := inferInstance }

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
