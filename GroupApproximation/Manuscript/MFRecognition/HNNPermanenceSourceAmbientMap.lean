import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceBaseToCoronaInjective

/-! The source edge algebra identified with its corona image. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

def sourceAmbientMap (data : CoronaConjugator G S T phi A X) :
    sourceEdgeAlgebra data ≃⋆ₐ[ℂ] sourceAmbient data :=
  starSubalgebraMapEquivOfInjective (sourceEdgeAlgebra data)
    (baseToCorona data) (baseToCorona_injective data)

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
