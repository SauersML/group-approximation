import GroupApproximation.Analysis.FiniteDimensionalCStarWedderburn
import Mathlib.Algebra.Central.End
import Mathlib.Analysis.InnerProductSpace.Adjoint
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

/-- The adjoint of an invertible linear map is again invertible; its inverse
is the adjoint of the inverse. -/
def adjointLinearEquiv
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V ≃ₗ[ℂ] V) : V ≃ₗ[ℂ] V where
  toFun := T.toLinearMap.adjoint
  invFun := T.symm.toLinearMap.adjoint
  left_inv x := by
    have hcomp : T.toLinearMap ∘ₗ T.symm.toLinearMap =
        (LinearMap.id : Module.End ℂ V) := by
      ext y
      simp
    have hadj := congrArg (fun A : Module.End ℂ V ↦ A.adjoint) hcomp
    have hx := congrArg (fun A : Module.End ℂ V ↦ A x) hadj
    simpa using hx
  right_inv x := by
    have hcomp : T.symm.toLinearMap ∘ₗ T.toLinearMap =
        (LinearMap.id : Module.End ℂ V) := by
      ext y
      simp
    have hadj := congrArg (fun A : Module.End ℂ V ↦ A.adjoint) hcomp
    have hx := congrArg (fun A : Module.End ℂ V ↦ A x) hadj
    simpa using hx
  map_add' x y := by simp
  map_smul' c x := by simp

@[simp] theorem adjointLinearEquiv_apply
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V ≃ₗ[ℂ] V) (x : V) :
    adjointLinearEquiv T x = T.toLinearMap.adjoint x := rfl

@[simp] theorem adjointLinearEquiv_symm
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V ≃ₗ[ℂ] V) :
    (adjointLinearEquiv T).symm = adjointLinearEquiv T.symm := by
  ext x
  rfl

/-- Taking the adjoint of an inner automorphism replaces its conjugator by
the adjoint of the inverse. -/
theorem star_conjAlgEquiv_apply
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V ≃ₗ[ℂ] V)
    (A : Module.End ℂ V) :
    star (T.conjAlgEquiv ℂ A) =
      (adjointLinearEquiv T.symm).conjAlgEquiv ℂ (star A) := by
  ext x
  simp [LinearEquiv.conjAlgEquiv_apply, adjointLinearEquiv,
    LinearMap.star_eq_adjoint]

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
  simp [transportedInvolution]

theorem transportedInvolution_mul
    {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
    (e : D ≃ₐ[ℂ] B) (x y : B) :
    transportedInvolution e (x * y) =
      transportedInvolution e y * transportedInvolution e x := by
  simp [transportedInvolution]

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
  simp [transportedInvolution]

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
    simp [transportedInvolution]
  map_mul' x y := by
    simp [transportedInvolution]
  commutes' c := by
    simp [transportedInvolution]

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
  exact LinearEquiv.conjAlgEquiv_surjective ℂ V V
    (transportedInvolutionAutomorphism e)

/-- Involutivity forces the product of the inverse-adjoint conjugator and
the original conjugator to be scalar.  This is the precise algebraic phase
normalization supplied by the center theorem for an endomorphism algebra. -/
theorem exists_scalar_adjointInverse_trans_conjugator
    {D V : Type*} [CStarAlgebra D] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (e : D ≃ₐ[ℂ] Module.End ℂ V) (T : V ≃ₗ[ℂ] V)
    (hT : T.conjAlgEquiv ℂ = transportedInvolutionAutomorphism e) :
    ∃ α : ℂˣ,
      (adjointLinearEquiv T.symm).trans T =
        α • (LinearEquiv.refl ℂ V) := by
  let U := adjointLinearEquiv T.symm
  have hstar (A : Module.End ℂ V) :
      U.conjAlgEquiv ℂ A = star (T.conjAlgEquiv ℂ (star A)) := by
    simpa only [U, star_star] using (star_conjAlgEquiv_apply T (star A)).symm
  have hconj :
      (U.trans T).conjAlgEquiv ℂ =
        (LinearEquiv.refl ℂ V).conjAlgEquiv ℂ := by
    ext A
    calc
      (U.trans T).conjAlgEquiv ℂ A =
          T.conjAlgEquiv ℂ (U.conjAlgEquiv ℂ A) := by
        ext x
        simp [LinearEquiv.conjAlgEquiv_apply, U]
      _ = transportedInvolutionAutomorphism e (U.conjAlgEquiv ℂ A) := by
        rw [hT]
      _ = transportedInvolutionAutomorphism e
          (star (T.conjAlgEquiv ℂ (star A))) := by rw [hstar]
      _ = transportedInvolutionAutomorphism e
          (star (transportedInvolutionAutomorphism e (star A))) := by rw [hT]
      _ = A := by
        simp only [transportedInvolutionAutomorphism_apply, star_star,
          transportedInvolution_involutive]
      _ = (LinearEquiv.refl ℂ V).conjAlgEquiv ℂ A := by simp
  exact LinearEquiv.conjAlgEquiv_ext_iff'
    ((adjointLinearEquiv T.symm).trans T) (LinearEquiv.refl ℂ V) |>.mp hconj

/-- The scalar relation supplied by the center theorem is equivalently a
phase relation between the conjugator and its adjoint. -/
theorem conjugator_eq_smul_adjoint_of_adjointInverse_trans_eq_smul_refl
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V ≃ₗ[ℂ] V) (α : ℂˣ)
    (hscalar :
      (adjointLinearEquiv T.symm).trans T =
        α • (LinearEquiv.refl ℂ V)) :
    T = α • adjointLinearEquiv T := by
  ext x
  have hx := DFunLike.congr_fun hscalar (adjointLinearEquiv T x)
  simpa using hx

/-- Every Skolem--Noether conjugator for the transported involution is a
unit scalar multiple of its adjoint. -/
theorem exists_scalar_conjugator_eq_smul_adjoint
    {D V : Type*} [CStarAlgebra D] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (e : D ≃ₐ[ℂ] Module.End ℂ V) (T : V ≃ₗ[ℂ] V)
    (hT : T.conjAlgEquiv ℂ = transportedInvolutionAutomorphism e) :
    ∃ α : ℂˣ, T = α • adjointLinearEquiv T := by
  obtain ⟨α, hα⟩ := exists_scalar_adjointInverse_trans_conjugator e T hT
  exact ⟨α,
    conjugator_eq_smul_adjoint_of_adjointInverse_trans_eq_smul_refl T α hα⟩

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
#audit_axioms exists_scalar_adjointInverse_trans_conjugator
#audit_axioms conjugator_eq_smul_adjoint_of_adjointInverse_trans_eq_smul_refl
#audit_axioms exists_scalar_conjugator_eq_smul_adjoint
#audit_axioms exists_conjugatingLinearEquiv_formula_for_transportedInvolution
