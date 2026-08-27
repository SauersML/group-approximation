import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaOperations

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-! ## `C = B₀ ⊕ B₁`, `A₁ = M₂(D)`, `A₂ = M₂(B₀)` -/

/-- Printed: *"Let `C = B₀ ⊕ B₁`"*. -/
abbrev edgeSumAlgebra (data : CoronaConjugator G S T phi A X) : Type :=
  sourceEdgeAlgebra data × targetEdgeAlgebra data

/-- Printed: *"`A₁ = M₂(D)`"*. -/
abbrev matrixBaseAlgebra (data : CoronaConjugator G S T phi A X) : Type :=
  CStarMatrix (Fin 2) (Fin 2) (baseAlgebra data)

/-- Printed: *"`A₂ = M₂(B₀)`"*. -/
abbrev matrixEdgeAlgebra (data : CoronaConjugator G S T phi A X) : Type :=
  CStarMatrix (Fin 2) (Fin 2) (sourceEdgeAlgebra data)

/-- Printed: *"`ι_A(c₀, c₁) = diag(c₀, c₁) ∈ A₁`"*. -/
def amalgamLeftInclusion (data : CoronaConjugator G S T phi A X) :
    edgeSumAlgebra data →⋆ₐ[ℂ] matrixBaseAlgebra data :=
  diagonalPairHom (sourceEdgeAlgebra data).subtype
    (targetEdgeAlgebra data).subtype

/-- Printed: *"`ι_B(c₀, c₁) = diag(c₀, Θ⁻¹(c₁)) ∈ A₂`"*. -/
def amalgamRightInclusion (data : CoronaConjugator G S T phi A X) :
    edgeSumAlgebra data →⋆ₐ[ℂ] matrixEdgeAlgebra data :=
  diagonalPairHom (StarAlgHom.id ℂ (sourceEdgeAlgebra data))
    (edgeIsomorphism data).symm.toStarAlgHom

@[simp] theorem amalgamLeftInclusion_apply
    (data : CoronaConjugator G S T phi A X) (c : edgeSumAlgebra data) :
    amalgamLeftInclusion data c =
      cStarDiagonalTwo ((c.1 : baseAlgebra data)) ((c.2 : baseAlgebra data)) :=
  diagonalPairHom_apply _ _ c

@[simp] theorem amalgamRightInclusion_apply
    (data : CoronaConjugator G S T phi A X) (c : edgeSumAlgebra data) :
    amalgamRightInclusion data c =
      cStarDiagonalTwo c.1 ((edgeIsomorphism data).symm c.2) :=
  diagonalPairHom_apply _ _ c

/-! ## The compatible corona pair `(φ_A, φ_B)` -/

/-- The inclusion of `D` in the corona. -/
def baseInclusion (data : CoronaConjugator G S T phi A X) :
    baseAlgebra data →⋆ₐ[ℂ] Corona X :=
  (baseAlgebra data).subtype

/-- The inclusion of `B₀` in the corona. -/
def sourceInclusion (data : CoronaConjugator G S T phi A X) :
    sourceEdgeAlgebra data →⋆ₐ[ℂ] Corona X :=
  (baseInclusion data).comp (sourceEdgeAlgebra data).subtype

@[simp] theorem baseInclusion_apply (data : CoronaConjugator G S T phi A X)
    (x : baseAlgebra data) : baseInclusion data x = (x : Corona X) :=
  rfl

@[simp] theorem sourceInclusion_apply (data : CoronaConjugator G S T phi A X)
    (x : sourceEdgeAlgebra data) :
    sourceInclusion data x = ((x : baseAlgebra data) : Corona X) :=
  rfl

/-- The two inclusions agree on `B₀`, in the shape the compatibility
computation needs: both sides are the same coercion, but only this spelling
lets `rw` close the goal without a deep definitional unfolding. -/
@[simp] theorem sourceInclusion_eq_baseInclusion
    (data : CoronaConjugator G S T phi A X) (x : sourceEdgeAlgebra data) :
    sourceInclusion data x = baseInclusion data ((x : baseAlgebra data)) :=
  rfl

theorem baseInclusion_injective (data : CoronaConjugator G S T phi A X) :
    Function.Injective (baseInclusion data) :=
  Subtype.val_injective

theorem sourceInclusion_injective (data : CoronaConjugator G S T phi A X) :
    Function.Injective (sourceInclusion data) :=
  (baseInclusion_injective data).comp Subtype.val_injective

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
