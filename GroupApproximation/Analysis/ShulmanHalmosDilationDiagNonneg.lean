import GroupApproximation.Analysis.ShulmanHalmosDilationDefectPositive

/-! Positivity of a two-by-two diagonal matrix. -/

namespace GroupApproximation
namespace ShulmanHalmosDilation

open scoped CStarAlgebra

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

noncomputable local instance : PartialOrder A := CStarAlgebra.spectralOrder A
noncomputable local instance : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

noncomputable local instance [Nontrivial A] :
    ContinuousFunctionalCalculus ℂ (Mat₂ A) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

noncomputable local instance [Nontrivial A] :
    ContinuousFunctionalCalculus ℝ (Mat₂ A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

noncomputable local instance [Nontrivial A] :
    PartialOrder (Mat₂ A) := CStarAlgebra.spectralOrder (Mat₂ A)

noncomputable local instance [Nontrivial A] :
    StarOrderedRing (Mat₂ A) := CStarAlgebra.spectralOrderedRing (Mat₂ A)

noncomputable local instance [Nontrivial A] :
    NonnegSpectrumClass ℝ (Mat₂ A) :=
  CStarAlgebra.instNonnegSpectrumClass

theorem diag₂_nonneg {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ diag₂ a b := by
  let R : Mat₂ A := diag₂ (CFC.sqrt a) (CFC.sqrt b)
  have hfactor : diag₂ a b = star R * R := by
    apply CStarMatrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [R, diag₂, CStarMatrix.star_eq_conjTranspose,
        CStarMatrix.mul_apply, Fin.sum_univ_two,
        (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq,
        (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)).star_eq,
        CFC.sqrt_mul_sqrt_self a ha, CFC.sqrt_mul_sqrt_self b hb]
  rw [hfactor]
  exact star_mul_self_nonneg R
end

end ShulmanHalmosDilation
end GroupApproximation
