import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceEdgeAmbientClosureForward

/-! Backward closure transport in the edge isomorphism construction. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem backwardCoronaHom_mem (data : CoronaConjugator G S T phi A X)
    (x : targetEdgeAlgebra data) :
    backwardCoronaHom data (x : baseAlgebra data) ∈ sourceAmbient data := by
  have hx := mem_closure_of_mem_groupGeneratedCStar
    ((baseUnitaryHom data).comp (edgeHom phi)) x.property
  exact continuous_map_mem_of_mem_closure_adjoin (backwardCoronaHom data)
    (continuous_backwardCoronaHom data)
    (sourceAmbient data) (sourceAmbient_isClosed data)
    (by rintro _ ⟨s, rfl⟩; exact backwardCoronaHom_generator data s) hx
end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
