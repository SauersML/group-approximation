import GroupApproximation.Analysis.ContinuousAdjoinMapping
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceEdgeAmbientContinuous

/-! Forward closure transport in the edge isomorphism construction. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem forwardCoronaHom_mem (data : CoronaConjugator G S T phi A X)
    (x : sourceEdgeAlgebra data) :
    forwardCoronaHom data (x : baseAlgebra data) ∈ targetAmbient data := by
  have hx := mem_closure_of_mem_groupGeneratedCStar
    ((baseUnitaryHom data).comp S.subtype) x.property
  exact continuous_map_mem_of_mem_closure_adjoin (forwardCoronaHom data)
    (continuous_forwardCoronaHom data)
    (targetAmbient data) (targetAmbient_isClosed data)
    (by rintro _ ⟨s, rfl⟩; exact forwardCoronaHom_generator data s) hx

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
