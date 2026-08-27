import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCoronaFactors

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- Printed: the displayed computation

`φ_B(ι_B(c₀,c₁)) = diag(c₀, W Θ⁻¹(c₁) W*) = diag(c₀,c₁) = φ_A(ι_A(c₀,c₁))`,

*"because `Θ` is conjugation by `W`"*. -/
theorem coronaFactor_compatible_apply
    (data : CoronaConjugator G S T phi A X) (c : edgeSumAlgebra data) :
    coronaFactorRight data (amalgamRightInclusion data c) =
      coronaFactorLeft data (amalgamLeftInclusion data c) := by
  have hconj := edgeIsomorphism_conj data ((edgeIsomorphism data).symm c.2)
  rw [StarAlgEquiv.apply_symm_apply] at hconj
  have hconj2 : (data.W : Corona X) *
        baseInclusion data
          ((((edgeIsomorphism data).symm c.2 : sourceEdgeAlgebra data) :
            baseAlgebra data)) *
      star (data.W : Corona X) =
      baseInclusion data ((c.2 : baseAlgebra data)) :=
    hconj
  rw [coronaFactorRight_apply, amalgamRightInclusion_apply,
    coe_conjugatorMatrix, matrixTwoMap_diagonal, conj_cStarDiagonalTwo,
    coronaFactorLeft_apply, amalgamLeftInclusion_apply,
    matrixTwoMap_diagonal, one_mul, star_one, mul_one]
  change cStarDiagonalTwo
      (baseInclusion data ((c.1 : sourceEdgeAlgebra data) : baseAlgebra data))
      ((data.W : Corona X) *
        baseInclusion data
          ((((edgeIsomorphism data).symm c.2 : sourceEdgeAlgebra data) :
            baseAlgebra data)) * star (data.W : Corona X)) =
    cStarDiagonalTwo
      (baseInclusion data ((c.1 : sourceEdgeAlgebra data) : baseAlgebra data))
      (baseInclusion data ((c.2 : targetEdgeAlgebra data) : baseAlgebra data))
  rw [hconj2]

theorem coronaFactor_compatible (data : CoronaConjugator G S T phi A X) :
    (coronaFactorLeft data).comp (amalgamLeftInclusion data) =
      (coronaFactorRight data).comp (amalgamRightInclusion data) := by
  apply StarAlgHom.ext
  intro c
  exact (coronaFactor_compatible_apply data c).symm

/-- The compatible pair `(φ_A, φ_B)` as a member of the representation family
defining the full amalgam. -/
def coronaAmalgamRepresentation (data : CoronaConjugator G S T phi A X) :
    CStarAmalgamRepresentation
      (C := edgeSumAlgebra data) (A := matrixBaseAlgebra data)
      (B := matrixEdgeAlgebra data)
     (amalgamLeftInclusion data)
      (amalgamRightInclusion data) :=
  CStarAmalgamRepresentation.ofCompatiblePair
      (C := edgeSumAlgebra data) (A := matrixBaseAlgebra data)
      (B := matrixEdgeAlgebra data)
    (amalgamLeftInclusion data) (amalgamRightInclusion data) (coronaFactorLeft data)
    (coronaFactorRight data) (coronaFactor_compatible data)

instance nonempty_coronaAmalgamRepresentation
    (data : CoronaConjugator G S T phi A X) :
    Nonempty (CStarAmalgamRepresentation
      (C := edgeSumAlgebra data) (A := matrixBaseAlgebra data)
      (B := matrixEdgeAlgebra data)
      (amalgamLeftInclusion data)
      (amalgamRightInclusion data)) :=
  ⟨coronaAmalgamRepresentation data⟩

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
