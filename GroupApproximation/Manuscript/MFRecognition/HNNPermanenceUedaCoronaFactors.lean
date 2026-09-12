import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaBasicMaps

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The unitary `diag(1, W)` of `M₂(𝒬)`.

Built directly in the matrix algebra from `cStarDiagonalTwo_mul`,
`star_cStarDiagonalTwo` and `cStarDiagonalTwo_one`, rather than by transporting
a unitary of `𝒬 × 𝒬`: the latter route asks for a `CStarAlgebra` structure on
the product, which is a far larger unification problem than the three
componentwise identities used here. -/
def conjugatorMatrix (data : CoronaConjugator G S T phi A X) :
    unitary (CStarMatrix (Fin 2) (Fin 2) (Corona X)) :=
  ⟨cStarDiagonalTwo (1 : Corona X) (data.W : Corona X), by
    constructor
    · rw [star_cStarDiagonalTwo, cStarDiagonalTwo_mul, star_one, one_mul,
        data.W.property.1, cStarDiagonalTwo_one]
    · rw [star_cStarDiagonalTwo, cStarDiagonalTwo_mul, star_one, mul_one,
        data.W.property.2, cStarDiagonalTwo_one]⟩

@[simp] theorem coe_conjugatorMatrix (data : CoronaConjugator G S T phi A X) :
    ((conjugatorMatrix data :
        unitary (CStarMatrix (Fin 2) (Fin 2) (Corona X))) :
      CStarMatrix (Fin 2) (Fin 2) (Corona X)) =
      cStarDiagonalTwo (1 : Corona X) (data.W : Corona X) :=
  rfl

/-- Printed: *"let `φ_A : M₂(D) → M₂(𝒬)` be the entrywise inclusion"*. -/
def coronaFactorLeft (data : CoronaConjugator G S T phi A X) :
    matrixBaseAlgebra data →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) (Corona X) :=
  matrixTwoMap (baseInclusion data)

/-- Printed: *"and `φ_B : M₂(B₀) → M₂(𝒬)` the entrywise inclusion followed by
conjugation by `diag(1, W)`"*. -/
def coronaFactorRight (data : CoronaConjugator G S T phi A X) :
    matrixEdgeAlgebra data →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) (Corona X) :=
  (Unitary.conjStarAlgAut ℂ (CStarMatrix (Fin 2) (Fin 2) (Corona X))
      (conjugatorMatrix data)).toStarAlgHom.comp
    (matrixTwoMap (sourceInclusion data))

@[simp] theorem coronaFactorLeft_apply
    (data : CoronaConjugator G S T phi A X) (M : matrixBaseAlgebra data) :
    coronaFactorLeft data M = matrixTwoMap (baseInclusion data) M :=
  rfl

@[simp] theorem coronaFactorRight_apply
    (data : CoronaConjugator G S T phi A X) (M : matrixEdgeAlgebra data) :
    coronaFactorRight data M =
      (conjugatorMatrix data : CStarMatrix (Fin 2) (Fin 2) (Corona X)) *
          matrixTwoMap (sourceInclusion data) M *
        star (conjugatorMatrix data :
          CStarMatrix (Fin 2) (Fin 2) (Corona X)) :=
  rfl

/-- Printed: *"Both are injective"*, first half. -/
theorem coronaFactorLeft_injective (data : CoronaConjugator G S T phi A X) :
    Function.Injective (coronaFactorLeft data) :=
  matrixTwoMap_injective (baseInclusion_injective data)

/-- Printed: *"Both are injective"*, second half. -/
theorem coronaFactorRight_injective (data : CoronaConjugator G S T phi A X) :
    Function.Injective (coronaFactorRight data) :=
  (EquivLike.injective
      (Unitary.conjStarAlgAut ℂ (CStarMatrix (Fin 2) (Fin 2) (Corona X))
        (conjugatorMatrix data))).comp
    (matrixTwoMap_injective (sourceInclusion_injective data))

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
