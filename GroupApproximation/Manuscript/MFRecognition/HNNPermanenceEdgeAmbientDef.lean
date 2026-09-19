import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceEdgeConjugationDef

/-! Ambient corona maps used to construct the edge isomorphism. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

def sourceAmbient (data : CoronaConjugator G S T phi A X) :
    StarSubalgebra ℂ (Corona X) :=
  (sourceEdgeAlgebra data).map (baseToCorona data)

def targetAmbient (data : CoronaConjugator G S T phi A X) :
    StarSubalgebra ℂ (Corona X) :=
  (targetEdgeAlgebra data).map (baseToCorona data)

def forwardCoronaHom (data : CoronaConjugator G S T phi A X) :
    baseAlgebra data →⋆ₐ[ℂ] Corona X :=
  (coronaConjugation data).toStarAlgHom.comp (baseToCorona data)

def backwardCoronaHom (data : CoronaConjugator G S T phi A X) :
    baseAlgebra data →⋆ₐ[ℂ] Corona X :=
  (coronaConjugation data).symm.toStarAlgHom.comp (baseToCorona data)

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
