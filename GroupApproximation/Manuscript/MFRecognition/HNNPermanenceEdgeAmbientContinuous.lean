import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceEdgeAmbientGenerators

/-! Continuity of the two ambient corona maps. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem continuous_forwardCoronaHom
    (data : CoronaConjugator G S T phi A X) :
    Continuous (forwardCoronaHom data) := by
  change Continuous fun y : baseAlgebra data ↦
    (data.W : Corona X) * (y : Corona X) * star (data.W : Corona X)
  fun_prop

theorem continuous_backwardCoronaHom
    (data : CoronaConjugator G S T phi A X) :
    Continuous (backwardCoronaHom data) := by
  change Continuous fun y : baseAlgebra data ↦
    star (data.W : Corona X) * (y : Corona X) * (data.W : Corona X)
  fun_prop

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
