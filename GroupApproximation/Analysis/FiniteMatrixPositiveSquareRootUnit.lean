import GroupApproximation.Analysis.FiniteMatrixPositiveSquareRoot

/-!
# Invertibility of the positive square root

The square of the CFC root is the sign-normalized conjugator.  Since the
latter is a nonzero scalar multiple of a linear equivalence, it is bijective.
Bijectivity of a square forces bijectivity, hence invertibility, of its root.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

noncomputable section

/-- If the square of a continuous endomorphism is bijective, then the
endomorphism itself is bijective. -/
theorem continuousLinearMap_bijective_of_sq_bijective
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {R A : V →L[ℂ] V} (hsquare : R * R = A)
    (hA : Function.Bijective A) : Function.Bijective R := by
  constructor
  · intro x y hxy
    apply hA.1
    have hx := congrArg (fun T : V →L[ℂ] V ↦ T x) hsquare
    have hy := congrArg (fun T : V →L[ℂ] V ↦ T y) hsquare
    change R (R x) = A x at hx
    change R (R y) = A y at hy
    exact hx.symm.trans ((congrArg R hxy).trans hy)
  · intro y
    obtain ⟨x, hx⟩ := hA.2 y
    refine ⟨R x, ?_⟩
    have hsquarex := congrArg (fun T : V →L[ℂ] V ↦ T x) hsquare
    change R (R x) = A x at hsquarex
    exact hsquarex.trans hx

/-- A continuous endomorphism with bijective square is a unit in the
continuous-operator algebra. -/
theorem continuousLinearMap_isUnit_of_sq_bijective
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V]
    {R A : V →L[ℂ] V} (hsquare : R * R = A)
    (hA : Function.Bijective A) : IsUnit R :=
  ContinuousLinearMap.isUnit_iff_bijective.mpr
    (continuousLinearMap_bijective_of_sq_bijective hsquare hA)

/-- A continuous operator whose underlying linear map is a real sign times a
linear equivalence is bijective. -/
theorem signed_linearEquiv_continuousLinearMap_bijective
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V]
    (S : V ≃ₗ[ℂ] V) (A : V →L[ℂ] V) {sign : ℝ}
    (hsign : sign = 1 ∨ sign = -1)
    (hA : A.toLinearMap = (sign : ℂ) • S.toLinearMap) :
    Function.Bijective A := by
  have hAapply (x : V) : A x = (((sign : ℂ) • S.toLinearMap) x) :=
    LinearMap.congr_fun hA x
  rcases hsign with rfl | rfl
  · have hAeq (x : V) : A x = S x := by simpa using hAapply x
    constructor
    · intro x y hxy
      apply S.injective
      rw [← hAeq x, ← hAeq y, hxy]
    · intro y
      obtain ⟨x, hx⟩ := S.surjective y
      exact ⟨x, (hAeq x).trans hx⟩
  · have hAeq (x : V) : A x = -(S x) := by simpa using hAapply x
    constructor
    · intro x y hxy
      apply S.injective
      apply neg_injective
      rw [← hAeq x, ← hAeq y, hxy]
    · intro y
      obtain ⟨x, hx⟩ := S.surjective (-y)
      refine ⟨x, ?_⟩
      rw [hAeq, hx, neg_neg]

/-- The positive square root of the sign-normalized conjugator is invertible.
This is the operator needed for the final similarity correction. -/
theorem exists_positive_unit_squareRoot_of_inverseForm_anisotropic
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V]
    (S : V ≃ₗ[ℂ] V) (hS : S.toLinearMap.IsSymmetric)
    (haniso : ∀ w : V, w ≠ 0 → inner ℂ w (S.symm w) ≠ 0) :
    ∃ (sign : ℝ) (A R : V →L[ℂ] V),
      (sign = 1 ∨ sign = -1) ∧
      A.toLinearMap = (sign : ℂ) • S.toLinearMap ∧
      A.IsPositive ∧ IsSelfAdjoint R ∧ R * R = A ∧ IsUnit R := by
  letI := FiniteDimensional.complete ℂ V
  obtain ⟨sign, A, R, hsign, hA, hApos, hRself, hRsquare⟩ :=
    exists_positive_squareRoot_of_inverseForm_anisotropic S hS haniso
  have hAbij : Function.Bijective A :=
    signed_linearEquiv_continuousLinearMap_bijective S A hsign hA
  have hRunit : IsUnit R :=
    continuousLinearMap_isUnit_of_sq_bijective hRsquare hAbij
  exact ⟨sign, A, R, hsign, hA, hApos, hRself, hRsquare, hRunit⟩

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms continuousLinearMap_bijective_of_sq_bijective
#audit_axioms continuousLinearMap_isUnit_of_sq_bijective
#audit_axioms signed_linearEquiv_continuousLinearMap_bijective
#audit_axioms exists_positive_unit_squareRoot_of_inverseForm_anisotropic
