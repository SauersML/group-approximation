import GroupApproximation.Analysis.StarSubalgebraMapEquiv
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceEdgeAmbientClosure

/-! Injectivity of the base inclusion into the corona. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem baseToCorona_injective (data : CoronaConjugator G S T phi A X) :
    Function.Injective (baseToCorona data) := by
  intro x y hxy
  exact Subtype.ext hxy

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
