import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceSourceAmbientMap

/-! The target edge algebra identified with its corona image. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

def targetAmbientMap (data : CoronaConjugator G S T phi A X) :
    targetEdgeAlgebra data ≃⋆ₐ[ℂ] targetAmbient data :=
  starSubalgebraMapEquivOfInjective (targetEdgeAlgebra data)
    (baseToCorona data) (baseToCorona_injective data)
end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
