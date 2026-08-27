import GroupApproximation.Manuscript.MFRecognition.HNNTraceReducedSubgroupCore
import GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
import GroupApproximation.Algebra.CountableInstances

/-!
# The reduced subgroup map for an HNN extension
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
open ReducedGroupCStarTrace

noncomputable section

/-- The printed homomorphism `C*_r(G) → C*_r(R)`. -/
def reducedSubgroupHom (H : Type) [Group H]
    (S₀ T₀ : Subgroup H) (psi : S₀ ≃* T₀) :
    ReducedGroupCStar H →⋆ₐ[ℂ] ReducedGroupCStar (HNNExtension H S₀ T₀ psi) :=
  reducedGroupCStarMapOfInjective HNNExtension.of
    (hnnExtension_base_injective psi)

@[simp] theorem reducedSubgroupHom_apply (H : Type)
    [Group H] (S₀ T₀ : Subgroup H) (psi : S₀ ≃* T₀) (g : H) :
    reducedSubgroupHom H S₀ T₀ psi (reducedLeftRegular H g) =
      reducedLeftRegular (HNNExtension H S₀ T₀ psi) (HNNExtension.of g) :=
  reducedGroupCStarMapOfInjective_apply HNNExtension.of
    (hnnExtension_base_injective psi) g

/-- The printed group `R` of `eq:hnn` is countable. -/
theorem hnnExtension_countable (H : Type) [Group H]
    [Countable H] (S₀ T₀ : Subgroup H) (psi : S₀ ≃* T₀) :
    Countable (HNNExtension H S₀ T₀ psi) := by
  delta HNNExtension
  letI : Countable (Multiplicative ℤ) :=
    CountableInstances.multiplicativeIntCountable
  letI : Countable (Monoid.Coprod H (Multiplicative ℤ)) :=
    Monoid.Coprod.mk_surjective.countable
  exact Con.mk'_surjective.countable

end


end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
