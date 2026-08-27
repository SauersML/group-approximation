import GroupApproximation.Analysis.MFAlgebraAmalgamFactorMap

/-! # Generator formulas for the factor-amalgam map -/

namespace GroupApproximation
namespace MFAlgebraAmalgamCriterion

noncomputable section

variable {C A B D E : Type}
  [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
  [CStarAlgebra D] [Nontrivial D] [CStarAlgebra E] [Nontrivial E]

@[simp] theorem factorAmalgamToSymmetricTarget_left
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    (gamma : C →⋆ₐ[ℂ] D)
    (alpha : A →⋆ₐ[ℂ] D) (beta : B →⋆ₐ[ℂ] D)
    (hA : alpha.comp iA = gamma) (hB : beta.comp iB = gamma)
    (e : UniversalCStarAmalgam gamma gamma →⋆ₐ[ℂ] E) (a : A) :
    factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB e
        (universalCStarAmalgamLeft iA iB a) =
      e (universalCStarAmalgamLeft gamma gamma (alpha a)) :=
  rfl

@[simp] theorem factorAmalgamToSymmetricTarget_right
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    (gamma : C →⋆ₐ[ℂ] D)
    (alpha : A →⋆ₐ[ℂ] D) (beta : B →⋆ₐ[ℂ] D)
    (hA : alpha.comp iA = gamma) (hB : beta.comp iB = gamma)
    (e : UniversalCStarAmalgam gamma gamma →⋆ₐ[ℂ] E) (b : B) :
    factorAmalgamToSymmetricTarget iA iB gamma alpha beta hA hB e
        (universalCStarAmalgamRight iA iB b) =
      e (universalCStarAmalgamRight gamma gamma (beta b)) :=
  rfl

end

end MFAlgebraAmalgamCriterion
end GroupApproximation
