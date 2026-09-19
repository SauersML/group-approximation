import GroupApproximation.Analysis.MFAlgebraAmalgamFactorRepresentation

/-! # The induced factor-amalgam map through a symmetric-double target -/

namespace GroupApproximation
namespace MFAlgebraAmalgamCriterion

noncomputable section

variable {C A B D E : Type}
  [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
  [CStarAlgebra D] [Nontrivial D] [CStarAlgebra E] [Nontrivial E]

def factorAmalgamToSymmetricTarget
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    (gamma : C →⋆ₐ[ℂ] D)
    (alpha : A →⋆ₐ[ℂ] D) (beta : B →⋆ₐ[ℂ] D)
    (hA : alpha.comp iA = gamma) (hB : beta.comp iB = gamma)
    (e : UniversalCStarAmalgam gamma gamma →⋆ₐ[ℂ] E) :
    UniversalCStarAmalgam iA iB →⋆ₐ[ℂ] E :=
  universalCStarAmalgamEval iA iB
    (factorToSymmetricTargetRepresentation iA iB gamma alpha beta hA hB e)

end

end MFAlgebraAmalgamCriterion
end GroupApproximation
