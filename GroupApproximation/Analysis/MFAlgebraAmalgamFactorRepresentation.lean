import GroupApproximation.Analysis.MFAlgebraSymmetricDoubleIdentity

/-! # A factor amalgam represented through a symmetric double -/

namespace GroupApproximation
namespace MFAlgebraAmalgamCriterion

noncomputable section

variable {C A B D E : Type}
  [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
  [CStarAlgebra D] [Nontrivial D] [CStarAlgebra E] [Nontrivial E]

def factorToSymmetricTargetRepresentation
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    (gamma : C →⋆ₐ[ℂ] D)
    (alpha : A →⋆ₐ[ℂ] D) (beta : B →⋆ₐ[ℂ] D)
    (hA : alpha.comp iA = gamma) (hB : beta.comp iB = gamma)
    (e : UniversalCStarAmalgam gamma gamma →⋆ₐ[ℂ] E) :
    CStarAmalgamRepresentation iA iB :=
  CStarAmalgamRepresentation.ofCompatiblePair iA iB
    (e.comp ((universalCStarAmalgamLeft gamma gamma).comp alpha))
    (e.comp ((universalCStarAmalgamRight gamma gamma).comp beta)) (by
      apply StarAlgHom.ext
      intro c
      change e (universalCStarAmalgamLeft gamma gamma (alpha (iA c))) =
        e (universalCStarAmalgamRight gamma gamma (beta (iB c)))
      rw [DFunLike.congr_fun hA c, DFunLike.congr_fun hB c]
      exact congrArg e
        (DFunLike.congr_fun
          (universalCStarAmalgam_compatible gamma gamma) c))

end

end MFAlgebraAmalgamCriterion
end GroupApproximation
