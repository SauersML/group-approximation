import GroupApproximation.Manuscript.MFRecognition.HNNTraceCovarianceGenerator

/-!
# Covariance of the reduced HNN pair
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

/-- The reduced pair satisfies the covariance relation on the full edge
algebra, by the generator-density theorem above. -/
theorem sigmaZero_covariance
    (data : CoronaConjugator G S T phi A X)
    (b : sourceEdgeAlgebra data) :
    (stableUnitary G S T phi :
          ReducedGroupCStar (HNNExtension G S T phi)) *
        sigmaZero data ((b : baseAlgebra data)) =
      sigmaZero data
          (((edgeIsomorphism data b : targetEdgeAlgebra data) :
            baseAlgebra data)) *
        (stableUnitary G S T phi :
          ReducedGroupCStar (HNNExtension G S T phi)) := by
  have hfg :
      (Unitary.conjStarAlgAut ℂ (ReducedGroupCStar (HNNExtension G S T phi))
              (stableUnitary G S T phi)).toStarAlgHom.comp
          ((sigmaZero data).comp (sourceEdgeAlgebra data).subtype) =
        (sigmaZero data).comp
          ((targetEdgeAlgebra data).subtype.comp
            (edgeIsomorphism data).toStarAlgHom) := by
    refine edgeDensity data _ _ ?_
    intro s
    show (stableUnitary G S T phi :
              ReducedGroupCStar (HNNExtension G S T phi)) *
            sigmaZero data
              ((((sourceGenerator data s :
                unitary (sourceEdgeAlgebra data)) : sourceEdgeAlgebra data) :
                baseAlgebra data)) *
          star (stableUnitary G S T phi :
            ReducedGroupCStar (HNNExtension G S T phi)) =
      sigmaZero data
        (((edgeIsomorphism data
            (((sourceGenerator data s : unitary (sourceEdgeAlgebra data)) :
              sourceEdgeAlgebra data)) : targetEdgeAlgebra data) :
          baseAlgebra data))
    rw [edgeIsomorphism_generator, coe_sourceGenerator, coe_targetGenerator]
    exact sigmaZero_covariance_generator data s
  have hb := congrArg
    (fun F : sourceEdgeAlgebra data →⋆ₐ[ℂ]
        ReducedGroupCStar (HNNExtension G S T phi) ↦ F b) hfg
  have hstar : star (stableUnitary G S T phi :
        ReducedGroupCStar (HNNExtension G S T phi)) *
      (stableUnitary G S T phi :
        ReducedGroupCStar (HNNExtension G S T phi)) = 1 :=
    (stableUnitary G S T phi).property.1
  have h : (stableUnitary G S T phi :
            ReducedGroupCStar (HNNExtension G S T phi)) *
          sigmaZero data ((b : baseAlgebra data)) *
        star (stableUnitary G S T phi :
          ReducedGroupCStar (HNNExtension G S T phi)) =
      sigmaZero data
        (((edgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data)) := hb
  calc
    (stableUnitary G S T phi :
          ReducedGroupCStar (HNNExtension G S T phi)) *
        sigmaZero data ((b : baseAlgebra data)) =
      ((stableUnitary G S T phi :
            ReducedGroupCStar (HNNExtension G S T phi)) *
          sigmaZero data ((b : baseAlgebra data)) *
        star (stableUnitary G S T phi :
          ReducedGroupCStar (HNNExtension G S T phi))) *
          (stableUnitary G S T phi :
            ReducedGroupCStar (HNNExtension G S T phi)) := by
              rw [mul_assoc, hstar, mul_one]
    _ = sigmaZero data
          (((edgeIsomorphism data b : targetEdgeAlgebra data) :
            baseAlgebra data)) *
        (stableUnitary G S T phi :
          ReducedGroupCStar (HNNExtension G S T phi)) := by rw [h]

end


end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
