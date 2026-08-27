import GroupApproximation.Analysis.FiniteMatrixSignNormalization
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Positive square root of the sign-normalized conjugator

The spectral sign normalization is first bundled as Mathlib positivity for a
continuous linear operator.  Continuous functional calculus then supplies a
self-adjoint square root whose square is the normalized operator.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

noncomputable section

/-- The sign-normalized conjugator is a positive continuous operator and is
the square of its self-adjoint continuous-functional-calculus square root. -/
theorem exists_positive_squareRoot_of_inverseForm_anisotropic
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V]
    (S : V ≃ₗ[ℂ] V) (hS : S.toLinearMap.IsSymmetric)
    (haniso : ∀ w : V, w ≠ 0 → inner ℂ w (S.symm w) ≠ 0) :
    ∃ (sign : ℝ) (A R : V →L[ℂ] V),
      (sign = 1 ∨ sign = -1) ∧
      A.toLinearMap = (sign : ℂ) • S.toLinearMap ∧
      A.IsPositive ∧ IsSelfAdjoint R ∧ R * R = A := by
  letI := FiniteDimensional.complete ℂ V
  obtain ⟨sign, hsign, hsymm, hform⟩ :=
    exists_sign_normalization_isSymmetric_and_form_nonneg S hS haniso
  let L : V →ₗ[ℂ] V := (sign : ℂ) • S.toLinearMap
  have hLpos : L.IsPositive := by
    refine ⟨hsymm, fun x ↦ ?_⟩
    rw [inner_re_symm]
    exact hform x
  let A : V →L[ℂ] V := L.toContinuousLinearMap
  have hApos : A.IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff L).mpr hLpos
  have hAnonneg : 0 ≤ A :=
    (ContinuousLinearMap.nonneg_iff_isPositive A).mpr hApos
  let R : V →L[ℂ] V := CFC.sqrt A
  have hRself : IsSelfAdjoint R :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)
  have hRsquare : R * R = A := by
    exact CFC.sqrt_mul_sqrt_self A hAnonneg
  exact ⟨sign, A, R, hsign, rfl, hApos, hRself, hRsquare⟩

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms exists_positive_squareRoot_of_inverseForm_anisotropic
