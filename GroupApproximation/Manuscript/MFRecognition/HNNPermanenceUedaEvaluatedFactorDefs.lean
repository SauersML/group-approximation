import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaEvaluatedConjugator
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaBasicMaps

/-! # The two evaluated Ueda factor maps -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open scoped CStarAlgebra Matrix

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

variable (data : CoronaConjugator G S T phi A X)

def evaluatedFactorLeft (R : HNNCoordinate data) :
    matrixBaseAlgebra data →⋆ₐ[ℂ]
      CStarMatrix (Fin 2) (Fin 2) R.carrier :=
  matrixTwoMap R.base

/-- The entrywise inclusion `M₂(B₀) → M₂(D)`. -/
def matrixEdgeInclusion : matrixEdgeAlgebra data →⋆ₐ[ℂ] matrixBaseAlgebra data :=
  matrixTwoMap (sourceEdgeAlgebra data).subtype

/-- The right factor, conjugated by `diag(1, R.stable)`.

The inclusion is composed at the matrix level on purpose.  Written at the
entry level, `R.base.comp (sourceEdgeAlgebra data).subtype` fails to
synthesize `Algebra ℂ ↥(sourceEdgeAlgebra data)`.  The subtype is not what
goes wrong -- the landed `sourceInclusion` composes with that same
`.subtype` and is green -- `R.base` is: its type is stated under the
`letI : CStarAlgebra carrier := instCStarAlgebra` of the
`CStarHNNRepresentation.base` field, so the instances it carries on the
middle algebra are not the ones the subtype supplies.  Here `R.base` meets
only `matrixTwoMap`, exactly as in `evaluatedFactorLeft`, and the two factors
are composed as maps of `CStarMatrix` algebras, whose instances come
uniformly from `matrixTwoCStarAlgebra`. -/
def evaluatedFactorRight (R : HNNCoordinate data) :
    matrixEdgeAlgebra data →⋆ₐ[ℂ]
      CStarMatrix (Fin 2) (Fin 2) R.carrier :=
  (Unitary.conjStarAlgAut ℂ (CStarMatrix (Fin 2) (Fin 2) R.carrier)
      (evaluatedConjugatorMatrix data R)).toStarAlgHom.comp
    ((matrixTwoMap R.base).comp (matrixEdgeInclusion data))

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
