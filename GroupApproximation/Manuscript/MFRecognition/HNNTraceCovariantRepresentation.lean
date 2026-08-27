import GroupApproximation.Manuscript.MFRecognition.HNNTraceCovariance

/-!
# The reduced covariant representation in the HNN trace argument
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

/-- The printed covariant pair `(σ₀, λ_R(t))`. -/
def reducedCovariantRepresentation
    (data : CoronaConjugator G S T phi A X) :
    CStarHNNRepresentation (sourceEdgeAlgebra data) (targetEdgeAlgebra data)
      (edgeIsomorphism data) :=
  CStarHNNRepresentation.ofCovariantPair (sourceEdgeAlgebra data)
    (targetEdgeAlgebra data) (edgeIsomorphism data)
    (sigmaZero data) (stableUnitary G S T phi)
    (sigmaZero_covariance data)

/-- Evaluation of the universal HNN algebra at the reduced covariant pair. -/
def sigma (data : CoronaConjugator G S T phi A X) :
    universalHNN data →⋆ₐ[ℂ] ReducedGroupCStar (HNNExtension G S T phi) :=
  universalCStarHNNEval (sourceEdgeAlgebra data) (targetEdgeAlgebra data)
    (edgeIsomorphism data) (reducedCovariantRepresentation data)

@[simp] theorem sigma_base
    (data : CoronaConjugator G S T phi A X) (d : baseAlgebra data) :
    sigma data (universalBase data d) = sigmaZero data d :=
  rfl

@[simp] theorem sigma_stable
    (data : CoronaConjugator G S T phi A X) :
    sigma data
        ((universalStable data : unitary (universalHNN data)) :
          universalHNN data) =
      (stableUnitary G S T phi :
        ReducedGroupCStar (HNNExtension G S T phi)) :=
  rfl

end


end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
