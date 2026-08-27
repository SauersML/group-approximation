import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUniversalDef

/-! The universal mapping property used in HNN permanence. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The universal mapping property used in the manuscript. -/
abbrev universalHNN_mappingProperty (data : CoronaConjugator G S T phi A X)
    {E : Type} [CStarAlgebra E] [Nontrivial E]
    (pi : baseAlgebra data →⋆ₐ[ℂ] E) (v : unitary E)
    (hcov : ∀ b : sourceEdgeAlgebra data,
      (v : E) * pi ((b : baseAlgebra data)) =
        pi (((edgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data)) * (v : E)) :=
  universalCStarHNN_mappingProperty (sourceEdgeAlgebra data)
    (targetEdgeAlgebra data) (edgeIsomorphism data) pi v hcov
end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
