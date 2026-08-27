import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceCoronaRepresentation

/-! The universal C-star HNN object and its canonical generators. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The manuscript's universal C-star HNN algebra. -/
abbrev universalHNN (data : CoronaConjugator G S T phi A X) : Type 1 :=
  UniversalCStarHNN (sourceEdgeAlgebra data) (targetEdgeAlgebra data)
    (edgeIsomorphism data)

/-- The image of `d ∈ D` in `U`. -/
def universalBase (data : CoronaConjugator G S T phi A X) :
    baseAlgebra data →⋆ₐ[ℂ] universalHNN data :=
  universalCStarHNNBase (sourceEdgeAlgebra data) (targetEdgeAlgebra data)
    (edgeIsomorphism data)

/-- The image of the canonical unitary generator `u` in `U`. -/
def universalStable (data : CoronaConjugator G S T phi A X) :
    unitary (universalHNN data) :=
  universalCStarHNNStable (sourceEdgeAlgebra data) (targetEdgeAlgebra data)
    (edgeIsomorphism data)

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
