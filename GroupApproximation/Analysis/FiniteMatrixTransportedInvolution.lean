import GroupApproximation.Analysis.FiniteDimensionalCStarWedderburn
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv

/-!
# The involution transported by an algebraic Wedderburn equivalence

An algebra equivalence need not preserve `star`.  Transporting the source
involution to the target gives a conjugate-linear involutive
anti-automorphism.  Composing it with the target involution gives an ordinary
complex-algebra automorphism.  Thus the blockwise star-classification problem
reduces exactly to innerness of an algebra automorphism of a full matrix
algebra, followed by the positivity analysis of its conjugating matrix.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

noncomputable section

/-- The involution on the target transported through a complex algebra
equivalence. -/
def transportedInvolution {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
    (e : D ≃ₐ[ℂ] B) (b : B) : B := e (star (e.symm b))

@[simp] theorem transportedInvolution_zero
    {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
    (e : D ≃ₐ[ℂ] B) : transportedInvolution e 0 = 0 := by
  simp [transportedInvolution]

@[simp] theorem transportedInvolution_one
    {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
    (e : D ≃ₐ[ℂ] B) : transportedInvolution e 1 = 1 := by
  simp [transportedInvolution]

theorem transportedInvolution_add
    {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
    (e : D ≃ₐ[ℂ] B) (x y : B) :
    transportedInvolution e (x + y) =
      transportedInvolution e x + transportedInvolution e y := by
  simp [transportedInvolution, star_add]

theorem transportedInvolution_mul
    {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
    (e : D ≃ₐ[ℂ] B) (x y : B) :
    transportedInvolution e (x * y) =
      transportedInvolution e y * transportedInvolution e x := by
  simp [transportedInvolution, star_mul]

/-- The target Gram element for the transported involution is exactly the
image of a genuine C-star Gram element in the source.  This is the analytic
positivity input available before the algebraic Wedderburn equivalence has
been corrected to preserve `star`. -/
theorem transportedInvolution_mul_self_eq_map_star_mul_self
    {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
    (e : D ≃ₐ[ℂ] B) (x : B) :
    transportedInvolution e x * x =
      e (star (e.symm x) * e.symm x) := by
  simp [transportedInvolution]

theorem transportedInvolution_smul
    {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
    (e : D ≃ₐ[ℂ] B) (c : ℂ) (x : B) :
    transportedInvolution e (c • x) =
      star c • transportedInvolution e x := by
  simp [transportedInvolution, star_smul]

@[simp] theorem transportedInvolution_involutive
    {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
    (e : D ≃ₐ[ℂ] B) (x : B) :
    transportedInvolution e (transportedInvolution e x) = x := by
  simp [transportedInvolution]

/-- Composing the transported involution with the target involution produces
an ordinary complex-algebra automorphism. -/
def transportedInvolutionAutomorphism
    {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
    (e : D ≃ₐ[ℂ] B) : B ≃ₐ[ℂ] B where
  toFun x := transportedInvolution e (star x)
  invFun x := star (transportedInvolution e x)
  left_inv x := by simp [transportedInvolution]
  right_inv x := by simp [transportedInvolution]
  map_add' x y := by
    simp [transportedInvolution, star_add]
  map_mul' x y := by
    simp [transportedInvolution, star_mul]
  commutes' c := by
    simp [transportedInvolution, star_smul]

@[simp] theorem transportedInvolutionAutomorphism_apply
    {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
    (e : D ≃ₐ[ℂ] B) (x : B) :
    transportedInvolutionAutomorphism e x =
      transportedInvolution e (star x) := rfl

/-- Exact reduction of the transported involution to the associated ordinary
algebra automorphism and the standard target involution. -/
theorem transportedInvolution_eq_automorphism_star
    {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
    (e : D ≃ₐ[ℂ] B) (x : B) :
    transportedInvolution e x = transportedInvolutionAutomorphism e (star x) := by
  simp [transportedInvolutionAutomorphism, transportedInvolution]

/-- Skolem--Noether, in Mathlib's endomorphism-algebra form, supplies an
actual conjugating linear equivalence for the ordinary automorphism associated
to a transported involution.  This is the algebraic innerness step, not an
assumption. -/
theorem exists_conjugatingLinearEquiv_for_transportedInvolution
    {D V : Type*} [CStarAlgebra D] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (e : D ≃ₐ[ℂ] Module.End ℂ V) :
    ∃ T : V ≃ₗ[ℂ] V,
      T.conjAlgEquiv ℂ = transportedInvolutionAutomorphism e := by
  exact LinearEquiv.conjAlgEquiv_surjective
    (transportedInvolutionAutomorphism e)

/-- The blockwise transported involution has the concrete Skolem--Noether
form `x ↦ T x⋆ T⁻¹` for an actual invertible complex-linear operator
`T`. -/
theorem exists_conjugatingLinearEquiv_formula_for_transportedInvolution
    {D V : Type*} [CStarAlgebra D] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (e : D ≃ₐ[ℂ] Module.End ℂ V) :
    ∃ T : V ≃ₗ[ℂ] V, ∀ x : Module.End ℂ V,
      transportedInvolution e x = T.conjAlgEquiv ℂ (star x) := by
  obtain ⟨T, hT⟩ := exists_conjugatingLinearEquiv_for_transportedInvolution e
  refine ⟨T, fun x ↦ ?_⟩
  rw [transportedInvolution_eq_automorphism_star, ← hT]

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms transportedInvolution_involutive
#audit_axioms transportedInvolution_mul_self_eq_map_star_mul_self
#audit_axioms transportedInvolutionAutomorphism
#audit_axioms transportedInvolution_eq_automorphism_star
#audit_axioms exists_conjugatingLinearEquiv_for_transportedInvolution
#audit_axioms exists_conjugatingLinearEquiv_formula_for_transportedInvolution
