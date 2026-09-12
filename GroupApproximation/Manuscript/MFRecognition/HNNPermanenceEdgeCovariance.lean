import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceEdgeIso

/-! The covariance identity for the edge isomorphism. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem edgeIsomorphism_covariance (data : CoronaConjugator G S T phi A X)
    (b : sourceEdgeAlgebra data) :
    (data.W : Corona X) *
        (baseAlgebra data).subtype ((b : baseAlgebra data)) =
      (baseAlgebra data).subtype
          (((edgeIsomorphism data b : targetEdgeAlgebra data) :
            baseAlgebra data)) *
        (data.W : Corona X) := by
  have hW : star (data.W : Corona X) * (data.W : Corona X) = 1 :=
    data.W.property.1
  have h : (data.W : Corona X) * ((b : baseAlgebra data) : Corona X) *
      star (data.W : Corona X) =
      (((edgeIsomorphism data b : targetEdgeAlgebra data) :
        baseAlgebra data) : Corona X) :=
    edgeIsomorphism_conj data b
  show (data.W : Corona X) * ((b : baseAlgebra data) : Corona X) =
    (((edgeIsomorphism data b : targetEdgeAlgebra data) :
      baseAlgebra data) : Corona X) * (data.W : Corona X)
  rw [← h, mul_assoc, hW, mul_one]

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
