import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceSetupEdges

/-! The ambient corona conjugation and base inclusion. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

def coronaConjugation (data : CoronaConjugator G S T phi A X) :
    Corona X ≃⋆ₐ[ℂ] Corona X :=
  Unitary.conjStarAlgAut ℂ (Corona X) data.W

def baseToCorona (data : CoronaConjugator G S T phi A X) :
    baseAlgebra data →⋆ₐ[ℂ] Corona X :=
  (baseAlgebra data).subtype

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
