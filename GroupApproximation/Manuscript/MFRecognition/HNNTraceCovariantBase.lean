import GroupApproximation.Manuscript.MFRecognition.HNNTraceReducedFactorization
import GroupApproximation.Manuscript.MFRecognition.HNNTraceReducedSubgroup

/-!
# The reduced base map in the HNN trace argument
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
open ReducedGroupCStarTrace

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- Printed: *"Composing, we obtain `σ₀ : D → C*_r(R)` with
`σ₀(ιρ(g)) = λ_R(g)`."* -/
def sigmaZero (data : CoronaConjugator G S T phi A X) :
    baseAlgebra data →⋆ₐ[ℂ] ReducedGroupCStar (HNNExtension G S T phi) :=
  (reducedSubgroupHom G S T phi).comp (reducedFactorisation data)

@[simp] theorem sigmaZero_apply
    (data : CoronaConjugator G S T phi A X) (g : G) :
    sigmaZero data
        (((baseUnitaryHom data g : unitary (baseAlgebra data)) :
          baseAlgebra data)) =
      reducedLeftRegular (HNNExtension G S T phi) (HNNExtension.of g) := by
  show reducedSubgroupHom G S T phi
      (reducedFactorisation data
        (((baseUnitaryHom data g : unitary (baseAlgebra data)) :
          baseAlgebra data))) = _
  rw [reducedFactorisation_apply, reducedSubgroupHom_apply]

/-- The stable unitary `λ_R(t)` of `C*_r(R)`. -/
def stableUnitary (H : Type) [Group H] (S₀ T₀ : Subgroup H)
    (psi : S₀ ≃* T₀) :
    unitary (ReducedGroupCStar (HNNExtension H S₀ T₀ psi)) :=
  reducedLeftRegularUnitary (HNNExtension H S₀ T₀ psi) HNNExtension.t

end


end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
