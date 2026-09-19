import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceConstructedEdgeConj

/-! Generator formula for the constructed edge isomorphism. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem constructedEdgeIsomorphism_generator
    (data : CoronaConjugator G S T phi A X) (s : S) :
    constructedEdgeIsomorphism data
        ((sourceGenerator data s : unitary (sourceEdgeAlgebra data)) :
          sourceEdgeAlgebra data) =
      ((targetGenerator data s : unitary (targetEdgeAlgebra data)) :
        targetEdgeAlgebra data) := by
  apply Subtype.ext
  apply baseToCorona_injective data
  rw [← constructedEdgeIsomorphism_conj]
  exact data.conjugates s
end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
