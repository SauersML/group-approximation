import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerUnitEleven
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerUnitRight

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNAmalgamCornerSentences

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-! ## Matrix-unit identities, isolated from the amalgam

Each obligation below is a fact about matrix units in `M₂` transported through
one of the two canonical factor maps.  The two layers are kept apart on
purpose: the matrix identity is proved where the landed `CStarMatrixTwo` simp
lemmas apply, and it is carried across the homomorphism with `map_star` /
`map_mul` and `congrArg`, both of which are applied by `exact` and so tolerate
the instance-path differences that made the earlier `rw` chains fail to match
syntactically. -/

theorem star_matrixUnitOne {K : Type} [CStarAlgebra K] (i j : Fin 2) :
    star (cStarMatrixUnitTwo i j (1 : K)) = cStarMatrixUnitTwo j i (1 : K) := by
  rw [star_cStarMatrixUnitTwo, star_one]

theorem matrixUnitOne_mul {K : Type} [CStarAlgebra K] (i j l : Fin 2) :
    cStarMatrixUnitTwo i j (1 : K) * cStarMatrixUnitTwo j l (1 : K) =
      cStarMatrixUnitTwo i l (1 : K) := by
  rw [cStarMatrixUnitTwo_mul]
  simp

/-! ## The corner word `e₁₂ f₂₁` -/

section CornerWord

variable (data : CoronaConjugator G S T phi A X)

theorem cornerUnit_star : star (cornerUnit data) = cornerUnit data := by
  show star (amalgamLeft data (cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data))) =
    amalgamLeft data (cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data))
  exact (map_star (amalgamLeft data)
      (cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data))).symm.trans
    (congrArg (amalgamLeft data) (star_matrixUnitOne 0 0))

theorem cornerUnit_mul :
    cornerUnit data * cornerUnit data = cornerUnit data := by
  show amalgamLeft data (cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data)) *
      amalgamLeft data (cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data)) =
    amalgamLeft data (cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data))
  exact (map_mul (amalgamLeft data)
      (cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data))
      (cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data))).symm.trans
    (congrArg (amalgamLeft data) (matrixUnitOne_mul 0 0 0))

/-- Printed: *"the partial isometry `e₁₂f₂₁`"* is a unitary of the corner
`ePe`.  The eleven matrix-unit identities below are exactly the hypotheses of
the repository's `manuscriptSentence_6e8a0c1082a2_cornerWordUnitary`. -/
theorem exists_cornerWord_unitary :
    ∃ w : unitary (CStarCorner (cornerUnit data) (cornerUnit_star data)
        (cornerUnit_mul data)),
      ((w : CStarCorner (cornerUnit data) (cornerUnit_star data)
          (cornerUnit_mul data)) : amalgam data) =
        matrixUnitLeft data 0 1 * matrixUnitRight data 1 0 := by
  refine manuscriptSentence_6e8a0c1082a2_cornerWordUnitary
    (cornerUnit data) (matrixUnitLeft data 0 1) (matrixUnitLeft data 1 0)
    (matrixUnitLeft data 1 1) (matrixUnitRight data 0 1)
    (matrixUnitRight data 1 0) (matrixUnitRight data 1 1)
    (cornerUnit_star data) (cornerUnit_mul data) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (matrixUnitLeft_one_one_eq_right data)
  · exact (map_star (amalgamLeft data) _).symm.trans
      (congrArg (amalgamLeft data) (star_matrixUnitOne 0 1))
  · exact (map_star (amalgamRight data) _).symm.trans
      (congrArg (amalgamRight data) (star_matrixUnitOne 1 0))
  · exact (map_mul (amalgamLeft data) _ _).symm.trans
      (congrArg (amalgamLeft data) (matrixUnitOne_mul 0 0 1))
  · rw [cornerUnit_eq_matrixUnitRight]
    exact (map_mul (amalgamRight data) _ _).symm.trans
      (congrArg (amalgamRight data) (matrixUnitOne_mul 1 0 0))
  · exact (map_mul (amalgamRight data) _ _).symm.trans
      (congrArg (amalgamRight data) (matrixUnitOne_mul 1 0 1))
  · exact (map_mul (amalgamLeft data) _ _).symm.trans
      (congrArg (amalgamLeft data) (matrixUnitOne_mul 0 1 1))
  · exact (map_mul (amalgamLeft data) _ _).symm.trans
      (congrArg (amalgamLeft data) (matrixUnitOne_mul 0 1 0))
  · exact (map_mul (amalgamLeft data) _ _).symm.trans
      (congrArg (amalgamLeft data) (matrixUnitOne_mul 1 0 1))
  · exact (map_mul (amalgamRight data) _ _).symm.trans
      (congrArg (amalgamRight data) (matrixUnitOne_mul 0 1 1))
  · rw [cornerUnit_eq_matrixUnitRight]
    exact (map_mul (amalgamRight data) _ _).symm.trans
      (congrArg (amalgamRight data) (matrixUnitOne_mul 0 1 0))

end CornerWord

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
