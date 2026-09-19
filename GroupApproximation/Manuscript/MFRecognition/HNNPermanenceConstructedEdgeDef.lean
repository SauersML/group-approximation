import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceEdgeAmbientRestriction

/-! The constructed edge isomorphism. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

def constructedEdgeIsomorphism (data : CoronaConjugator G S T phi A X) :
    sourceEdgeAlgebra data ≃⋆ₐ[ℂ] targetEdgeAlgebra data :=
  (sourceAmbientMap data).trans
    ((ambientEdgeEquiv data).trans (targetAmbientMap data).symm)

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
