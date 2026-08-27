import GroupApproximation.Manuscript.MFRecognition.HNNTraceEdgeDensity

/-!
# Covariance on the HNN edge generators
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

/-- The printed identity *"on the generators `ιρ(s)` both sides equal
`λ_R(θ(s))`, because `tst⁻¹ = θ(s)` in `R`"*. -/
theorem sigmaZero_covariance_generator
    (data : CoronaConjugator G S T phi A X) (s : S) :
    (stableUnitary G S T phi :
            ReducedGroupCStar (HNNExtension G S T phi)) *
          sigmaZero data
            (((baseUnitaryHom data (s : G) : unitary (baseAlgebra data)) :
              baseAlgebra data)) *
        star (stableUnitary G S T phi :
          ReducedGroupCStar (HNNExtension G S T phi)) =
      sigmaZero data
        (((baseUnitaryHom data (edgeHom phi s) :
          unitary (baseAlgebra data)) : baseAlgebra data)) := by
  have hgroup : (HNNExtension.t : HNNExtension G S T phi) *
      HNNExtension.of (s : G) * (HNNExtension.t : HNNExtension G S T phi)⁻¹ =
      HNNExtension.of ((phi s : T) : G) := by
    rw [HNNExtension.t_mul_of, mul_assoc, mul_inv_cancel, mul_one]
  rw [sigmaZero_apply, sigmaZero_apply, edgeHom_apply]
  show reducedLeftRegular (HNNExtension G S T phi) HNNExtension.t *
        reducedLeftRegular (HNNExtension G S T phi)
          (HNNExtension.of (s : G)) *
      star (reducedLeftRegular (HNNExtension G S T phi) HNNExtension.t) =
    reducedLeftRegular (HNNExtension G S T phi)
      (HNNExtension.of ((phi s : T) : G))
  rw [star_reducedLeftRegular, ← reducedLeftRegular_mul,
    ← reducedLeftRegular_mul, hgroup]

end


end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
