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

/-- Move a conjugation relation to a commutation relation, in a bare monoid.

Stated abstractly on purpose: at the concrete ambient
`ReducedGroupCStar (HNNExtension G S T phi)` the two rewrites this replaces
(`mul_assoc`/`mul_one` and the substitution of the conjugation hypothesis)
both drove `isDefEq` past its heartbeat budget, because every occurrence of
the stable unitary carries the full unitary-subtype coercion. Here the
carrier is a variable, so the rewrites cost nothing and the one expensive
unification happens once, at the application site. -/
theorem mul_eq_mul_of_conj_eq {R : Type*} [Monoid R] {u v x y : R}
    (hvu : v * u = 1) (h : u * x * v = y) : u * x = y * u := by
  calc
    u * x = u * x * (v * u) := by rw [hvu, mul_one]
    _ = u * x * v * u := by rw [← mul_assoc]
    _ = y * u := by rw [h]

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
  exact mul_eq_mul_of_conj_eq hstar h

end


end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
