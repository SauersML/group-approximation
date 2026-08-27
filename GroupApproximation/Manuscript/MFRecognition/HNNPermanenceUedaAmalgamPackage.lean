import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCompatibility

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

structure PackagedCStarAlgebra where
  carrier : Type 1
  instCStarAlgebra : CStarAlgebra carrier

instance : CoeSort PackagedCStarAlgebra (Type 1) :=
  ⟨PackagedCStarAlgebra.carrier⟩

noncomputable instance (P : PackagedCStarAlgebra) : CStarAlgebra P :=
  P.instCStarAlgebra

/-- Printed: *"let `P = A₁ *_C A₂` be the full amalgamated free product"*. -/
def amalgam (data : CoronaConjugator G S T phi A X) :
    PackagedCStarAlgebra where
  carrier := @UniversalCStarAmalgam
    (edgeSumAlgebra data) (matrixBaseAlgebra data) (matrixEdgeAlgebra data)
    inferInstance inferInstance inferInstance
    (amalgamLeftInclusion data) (amalgamRightInclusion data)
    ⟨coronaAmalgamRepresentation data⟩
  instCStarAlgebra := @universalCStarAmalgamCStarAlgebra
    (edgeSumAlgebra data) (matrixBaseAlgebra data) (matrixEdgeAlgebra data)
    inferInstance inferInstance inferInstance
    (amalgamLeftInclusion data) (amalgamRightInclusion data)
    ⟨coronaAmalgamRepresentation data⟩

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
