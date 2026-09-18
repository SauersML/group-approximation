import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinReduction
import Mathlib.Algebra.Polynomial.Coeff
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin monic route, part 2: Karoubi's normalization `σ(X) σ(0)⁻¹`

Lane `bh-met-41`.  Let `A` be a commutative ring with `SL_N(A) = E_N(A)`.  For
`σ ∈ SL_N(A[X])` put `v = σ(0) ∈ SL_N(A)` (the constant-coefficient image) and `w = C(v)`
(the same matrix, viewed over `A[X]`).  Then `v ∈ E_N(A)`, so `w ∈ E_N(A[X])`, and
`τ = σ w⁻¹` has determinant `1` and `τ(0) = v v⁻¹ = 1`.  Hence `SL_N(A[X]) = E_N(A[X])` as soon
as every **normalized** `τ ∈ SL_N(A[X])` (i.e. `τ(0) = 1`) is elementary
(`suslinMonic_specialLinearInElementary_polynomial_of_normalized`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- Every normalized determinant-one matrix over `A[X]` is elementary: `τ ∈ GL_N(A[X])`,
`det τ = 1` and `τ(0) = 1` imply `τ ∈ E_N(A[X])`. -/
def SuslinMonicNormalizedElementary (A : Type*) [CommRing A] (N : ℕ) : Prop :=
  ∀ τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A),
    Matrix.det (τ : Matrix (Fin N) (Fin N) (Polynomial A)) = 1 →
      elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) τ = 1 →
        τ ∈ elementaryGroup (Fin N) (Polynomial A)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinMonicNormalizedElementary

/-- Evaluating the constant matrix `C(v)` at `0` gives back `v`. -/
theorem suslinMonic_constantCoeff_map_C {A : Type*} [CommRing A] {N : ℕ}
    (v : Matrix.GeneralLinearGroup (Fin N) A) :
    elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A))
      (elementaryMatrixUnitMap (ι := Fin N) (Polynomial.C (R := A)) v) = v := by
  apply Units.ext
  ext i j
  change Polynomial.constantCoeff (Polynomial.C ((v : Matrix (Fin N) (Fin N) A) i j)) =
    (v : Matrix (Fin N) (Fin N) A) i j
  rw [Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_constantCoeff_map_C

/-- **Karoubi's normalization.**  If `SL_N(A) = E_N(A)` and every normalized
`τ ∈ SL_N(A[X])` is elementary, then `SL_N(A[X]) = E_N(A[X])`. -/
theorem suslinMonic_specialLinearInElementary_polynomial_of_normalized {A : Type*}
    [CommRing A] {N : ℕ} (hA : SpecialLinearInElementary A N)
    (hnorm : SuslinMonicNormalizedElementary A N) :
    SpecialLinearInElementary (Polynomial A) N := by
  intro σ hσ
  let v : Matrix.GeneralLinearGroup (Fin N) A :=
    elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) σ
  have hvval : (v : Matrix (Fin N) (Fin N) A) =
      (Polynomial.constantCoeff (R := A)).mapMatrix
        (σ : Matrix (Fin N) (Fin N) (Polynomial A)) := rfl
  have hv : Matrix.det (v : Matrix (Fin N) (Fin N) A) = 1 := by
    rw [hvval, ← RingHom.map_det, hσ, map_one]
  let w : Matrix.GeneralLinearGroup (Fin N) (Polynomial A) :=
    elementaryMatrixUnitMap (ι := Fin N) (Polynomial.C (R := A)) v
  have hw : w ∈ elementaryGroup (Fin N) (Polynomial A) :=
    elementaryGroup_map_le (Polynomial.C (R := A)) (Subgroup.mem_map_of_mem _ (hA v hv))
  have hww : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) w = v :=
    suslinMonic_constantCoeff_map_C v
  have hτdet : Matrix.det ((σ * w⁻¹ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A)) :
      Matrix (Fin N) (Fin N) (Polynomial A)) = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hσ,
      suslin_det_eq_one_of_mem_elementaryGroup (inv_mem hw), one_mul]
  have hτ0 : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A))
      (σ * w⁻¹) = 1 := by
    rw [map_mul, map_inv, hww]
    exact mul_inv_cancel v
  have hmem := mul_mem (hnorm (σ * w⁻¹) hτdet hτ0) hw
  rwa [inv_mul_cancel_right] at hmem

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_specialLinearInElementary_polynomial_of_normalized

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
