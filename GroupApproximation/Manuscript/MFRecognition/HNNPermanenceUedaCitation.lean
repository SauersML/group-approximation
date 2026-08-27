import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaDirectEmbedding

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-! ## The direct Ueda corner embedding -/

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Printed: *"In particular `U` embeds in `P`."*  The corner inclusion is not
unital, since the corner's unit is `e`, not the unit of `P`. -/
theorem universalHNN_embeds_amalgam (hUeda : UedaCornerMapStatement)
    (data : CoronaConjugator G S T phi A X) :
    ∃ Psi : universalHNN data →⋆ₙₐ[ℂ] amalgam data, Function.Injective Psi := by
  refine ⟨(CStarCorner.inclusion (cornerUnit data) (cornerUnit_star data)
      (cornerUnit_mul data)).comp
      (uedaCornerMap hUeda data).toNonUnitalStarAlgHom, ?_⟩
  intro x y hxy
  exact uedaCornerMap_injective hUeda data (Subtype.ext hxy)


end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
