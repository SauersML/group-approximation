import GroupApproximation.Analysis.UniversalCStarAmalgam

/-! # The identity coordinate of a symmetric full C-star amalgam -/

namespace GroupApproximation
namespace MFAlgebraAmalgamCriterion

noncomputable section

variable {C D : Type} [CStarAlgebra C] [CStarAlgebra D] [Nontrivial D]

def symmetricIdentityRepresentation (gamma : C →⋆ₐ[ℂ] D) :
    CStarAmalgamRepresentation gamma gamma :=
  CStarAmalgamRepresentation.ofCompatiblePair gamma gamma
    (StarAlgHom.id ℂ D) (StarAlgHom.id ℂ D) rfl

noncomputable instance symmetricAmalgamRepresentationNonempty
    (gamma : C →⋆ₐ[ℂ] D) :
    Nonempty (CStarAmalgamRepresentation gamma gamma) :=
  ⟨symmetricIdentityRepresentation gamma⟩

end

end MFAlgebraAmalgamCriterion
end GroupApproximation
