import GroupApproximation.Analysis.ShulmanHalmosDilationAlgebra

/-! Unitarity of the Halmos dilation. -/

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

/-- Multiplying the Halmos matrix by its adjoint gives the identity. -/
theorem halmos_mul_star [Nontrivial A] {x : A} (hx : ‖x‖ ≤ 1) :
    halmos x * star (halmos x) = 1 := by
  have hpull := leftDefect_mul_eq_mul_rightDefect hx
  have hpullStar := star_mul_leftDefect_eq_rightDefect_mul_star hx
  have hleftSq := leftDefect_mul_self hx
  have hrightSq := rightDefect_mul_self hx
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [halmos, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.mul_apply, Fin.sum_univ_two, star_leftDefect,
      star_rightDefect, hleftSq, hrightSq, hpull, hpullStar]

/-- Multiplying the adjoint of the Halmos matrix by the matrix also gives the
identity. -/
theorem star_halmos_mul [Nontrivial A] {x : A} (hx : ‖x‖ ≤ 1) :
    star (halmos x) * halmos x = 1 := by
  have hpull := leftDefect_mul_eq_mul_rightDefect hx
  have hpullStar := star_mul_leftDefect_eq_rightDefect_mul_star hx
  have hleftSq := leftDefect_mul_self hx
  have hrightSq := rightDefect_mul_self hx
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [halmos, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.mul_apply, Fin.sum_univ_two, star_leftDefect,
      star_rightDefect, hleftSq, hrightSq, hpull, hpullStar]

/-- The Halmos dilation of a contraction is a genuine unitary. -/
theorem halmos_mem_unitary [Nontrivial A] {x : A} (hx : ‖x‖ ≤ 1) :
    halmos x ∈ unitary (Mat₂ A) :=
  Unitary.mem_iff.2 ⟨star_halmos_mul hx, halmos_mul_star hx⟩

/-- The bundled Halmos unitary of a contraction. -/
def halmosUnitary [Nontrivial A] (x : A) (hx : ‖x‖ ≤ 1) : unitary (Mat₂ A) :=
  ⟨halmos x, halmos_mem_unitary hx⟩

@[simp] theorem coe_halmosUnitary [Nontrivial A] (x : A) (hx : ‖x‖ ≤ 1) :
    ((halmosUnitary x hx : unitary (Mat₂ A)) : Mat₂ A) = halmos x :=
  rfl

end

end ShulmanHalmosDilation
end GroupApproximation
