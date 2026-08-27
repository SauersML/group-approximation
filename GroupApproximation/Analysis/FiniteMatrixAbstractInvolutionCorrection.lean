import GroupApproximation.Analysis.FiniteMatrixCorrectedStarEquiv

/-!
# Correcting an abstract C-star-type involution on a full matrix algebra

The blockwise Wedderburn argument does not present each matrix block as the
image of a separate C-star algebra.  Instead, restriction of the transported
involution gives a conjugate-linear involutive anti-automorphism on the block,
and C-star cancellation gives `tau(x) * x = 0` only for `x = 0`.

This file isolates precisely those properties.  The Skolem--Noether,
self-adjoint rescaling, sign, and positive-square-root machinery already
proved for a transported involution then yields an algebra automorphism which
conjugates `tau` to the ordinary adjoint.  No classification or lifting input
is assumed.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

noncomputable section

/-- The exact algebraic and C-star cancellation data inherited by one block
of a transported involution. -/
structure FullMatrixInvolutionData
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] where
  tau : Module.End ℂ V → Module.End ℂ V
  map_zero : tau 0 = 0
  map_one : tau 1 = 1
  map_add : ∀ x y, tau (x + y) = tau x + tau y
  map_mul : ∀ x y, tau (x * y) = tau y * tau x
  map_smul : ∀ (c : ℂ) x, tau (c • x) = star c • tau x
  involutive : ∀ x, tau (tau x) = x
  gram_eq_zero_iff : ∀ x, tau x * x = 0 ↔ x = 0

namespace FullMatrixInvolutionData

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- Composing an abstract transported involution with the ordinary adjoint
is a complex-algebra automorphism. -/
def automorphism (J : FullMatrixInvolutionData V) :
    Module.End ℂ V ≃ₐ[ℂ] Module.End ℂ V where
  toFun x := J.tau (star x)
  invFun x := star (J.tau x)
  left_inv x := by
    change star (J.tau (J.tau (star x))) = x
    rw [J.involutive, star_star]
  right_inv x := by
    change J.tau (star (star (J.tau x))) = x
    rw [star_star, J.involutive]
  map_add' x y := by rw [star_add, J.map_add]
  map_mul' x y := by rw [star_mul, J.map_mul]
  commutes' c := by
    change J.tau (star (algebraMap ℂ (Module.End ℂ V) c)) =
      algebraMap ℂ (Module.End ℂ V) c
    rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one, J.map_smul,
      J.map_one, star_star]

@[simp] theorem automorphism_apply (J : FullMatrixInvolutionData V)
    (x : Module.End ℂ V) : J.automorphism x = J.tau (star x) := rfl

/-- Recover the anti-involution from its associated ordinary automorphism. -/
theorem tau_eq_automorphism_star (J : FullMatrixInvolutionData V)
    (x : Module.End ℂ V) : J.tau x = J.automorphism (star x) := by
  rw [automorphism_apply, star_star]

/-- Skolem--Noether supplies a conjugator for the associated automorphism. -/
theorem exists_conjugatingLinearEquiv (J : FullMatrixInvolutionData V)
    [Nontrivial V] :
    ∃ T : V ≃ₗ[ℂ] V, T.conjAlgEquiv ℂ = J.automorphism :=
  LinearEquiv.conjAlgEquiv_surjective ℂ V V J.automorphism

/-- Involutivity forces the inverse-adjoint conjugator followed by the
conjugator to be scalar. -/
theorem exists_scalar_adjointInverse_trans_conjugator
    (J : FullMatrixInvolutionData V) [Nontrivial V]
    (T : V ≃ₗ[ℂ] V) (hT : T.conjAlgEquiv ℂ = J.automorphism) :
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
    apply AlgEquiv.ext
    intro A
    calc
      (U.trans T).conjAlgEquiv ℂ A =
          T.conjAlgEquiv ℂ (U.conjAlgEquiv ℂ A) := by
        ext x
        simp [LinearEquiv.conjAlgEquiv_apply, U]
      _ = J.automorphism (U.conjAlgEquiv ℂ A) := by rw [hT]
      _ = J.automorphism (star (T.conjAlgEquiv ℂ (star A))) := by rw [hstar]
      _ = J.automorphism (star (J.automorphism (star A))) := by rw [hT]
      _ = A := by simp [automorphism, J.involutive]
      _ = (LinearEquiv.refl ℂ V).conjAlgEquiv ℂ A := by rfl
  exact LinearEquiv.conjAlgEquiv_ext_iff'
    ((adjointLinearEquiv T.symm).trans T) (LinearEquiv.refl ℂ V) |>.mp hconj

/-- The conjugator is a unit scalar multiple of its adjoint. -/
theorem exists_scalar_conjugator_eq_smul_adjoint
    (J : FullMatrixInvolutionData V) [Nontrivial V]
    (T : V ≃ₗ[ℂ] V) (hT : T.conjAlgEquiv ℂ = J.automorphism) :
    ∃ α : ℂˣ, T = α • adjointLinearEquiv T := by
  obtain ⟨α, hα⟩ := J.exists_scalar_adjointInverse_trans_conjugator T hT
  exact ⟨α,
    conjugator_eq_smul_adjoint_of_adjointInverse_trans_eq_smul_refl T α hα⟩

/-- A unit-scalar rescaling makes a Skolem--Noether conjugator genuinely
self-adjoint without changing its inner automorphism. -/
theorem exists_selfAdjoint_conjugator
    (J : FullMatrixInvolutionData V) [Nontrivial V] :
    ∃ S : V ≃ₗ[ℂ] V,
      S.conjAlgEquiv ℂ = J.automorphism ∧ adjointLinearEquiv S = S := by
  obtain ⟨T, hT⟩ := J.exists_conjugatingLinearEquiv
  obtain ⟨α, hα⟩ := J.exists_scalar_conjugator_eq_smul_adjoint T hT
  have hunit := unitScalar_star_mul_self_eq_one_of_eq_smul_adjoint T α hα
  obtain ⟨β, hβ⟩ := exists_unitScalar_mul_eq_star α hunit
  let S : V ≃ₗ[ℂ] V := β • T
  refine ⟨S, ?_, ?_⟩
  · rw [show S = β • T from rfl, unit_smul_conjAlgEquiv_eq, hT]
  · exact adjointLinearEquiv_unit_smul_eq_self T α β hα hβ

/-- Gram cancellation rules out isotropic vectors for the inverse form of a
conjugator implementing the abstract involution. -/
theorem conjugator_inverseForm_anisotropic
    (J : FullMatrixInvolutionData V)
    (S : V ≃ₗ[ℂ] V) (hS : S.conjAlgEquiv ℂ = J.automorphism)
    {w : V} (hw : w ≠ 0) : inner ℂ w (S.symm w) ≠ 0 := by
  intro hisotropic
  let A : Module.End ℂ V := innerRankOneEnd w w
  have hAne : A ≠ 0 := by
    intro hAzero
    have happ := congrArg (fun F : Module.End ℂ V ↦ F w) hAzero
    have hinner : inner ℂ w w ≠ 0 := inner_self_ne_zero.mpr hw
    have hAw : inner ℂ w w • w ≠ 0 := smul_ne_zero hinner hw
    apply hAw
    simpa [A] using happ
  have htransport (x : Module.End ℂ V) :
      J.tau x = S.conjAlgEquiv ℂ (star x) := by
    rw [J.tau_eq_automorphism_star, ← hS]
  have hGram : J.tau A * A = 0 := by
    ext v
    rw [Module.End.mul_apply, htransport]
    simp [LinearEquiv.conjAlgEquiv_apply, A, hisotropic]
  exact hAne ((J.gram_eq_zero_iff A).mp hGram)

/-- Every full-matrix involution with the transported C-star properties is
conjugate to the ordinary adjoint by an algebra automorphism. -/
theorem exists_intertwiningAlgEquiv
    (J : FullMatrixInvolutionData V) [Nontrivial V] :
    ∃ c : Module.End ℂ V ≃ₐ[ℂ] Module.End ℂ V,
      ∀ x, c (J.tau x) = star (c x) := by
  letI := FiniteDimensional.complete ℂ V
  obtain ⟨S, hSconj, hSadj⟩ := J.exists_selfAdjoint_conjugator
  have hSsymm : S.toLinearMap.IsSymmetric := by
    intro x y
    calc
      inner ℂ (S x) y = inner ℂ (adjointLinearEquiv S x) y := by rw [hSadj]
      _ = inner ℂ x (S y) :=
        LinearMap.adjoint_inner_left S.toLinearMap y x
  have hSaniso : ∀ w : V, w ≠ 0 → inner ℂ w (S.symm w) ≠ 0 :=
    fun w hw ↦ J.conjugator_inverseForm_anisotropic S hSconj hw
  obtain ⟨sign, A, R, hsign, hA, _hApos, hRself, hRsquare, hRunit⟩ :=
    exists_positive_unit_squareRoot_of_inverseForm_anisotropic S hSsymm hSaniso
  have hRbij : Function.Bijective R :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hRunit
  let U : V ≃ₗ[ℂ] V := LinearEquiv.ofBijective R.toLinearMap hRbij
  have hUsymm : U.toLinearMap.IsSymmetric := by
    intro x y
    change inner ℂ (R x) y = inner ℂ x (R y)
    exact hRself.isSymmetric x y
  have hUadj : adjointLinearEquiv U = U := by
    apply LinearEquiv.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    calc
      inner ℂ (adjointLinearEquiv U x) y = inner ℂ x (U y) :=
        LinearMap.adjoint_inner_left U.toLinearMap y x
      _ = inner ℂ (U x) y := (hUsymm x y).symm
  have hUtwo (x : V) : (U.trans U) x = (sign : ℂ) • S x := by
    have hRpoint := congrArg (fun T : V →L[ℂ] V ↦ T x) hRsquare
    change R (R x) = A x at hRpoint
    have hApoint := LinearMap.congr_fun hA x
    calc
      (U.trans U) x = R (R x) := by rfl
      _ = A x := hRpoint
      _ = (sign : ℂ) • S x := hApoint
  have hconjSquare :
      (U.trans U).conjAlgEquiv ℂ = S.conjAlgEquiv ℂ := by
    rcases hsign with rfl | rfl
    · apply (LinearEquiv.conjAlgEquiv_ext_iff' (U.trans U) S).mpr
      refine ⟨1, ?_⟩
      apply LinearEquiv.ext
      intro x
      simpa using hUtwo x
    · apply (LinearEquiv.conjAlgEquiv_ext_iff' (U.trans U) S).mpr
      refine ⟨(-1 : ℂˣ), ?_⟩
      apply LinearEquiv.ext
      intro x
      simpa using hUtwo x
  have hcancel (x : Module.End ℂ V) :
      U.symm.conjAlgEquiv ℂ (S.conjAlgEquiv ℂ x) =
        U.conjAlgEquiv ℂ x := by
    rw [← hconjSquare]
    ext v
    simp [LinearEquiv.conjAlgEquiv_apply]
  have hintertwine (x : Module.End ℂ V) :
      U.symm.conjAlgEquiv ℂ (J.tau x) =
        star (U.symm.conjAlgEquiv ℂ x) := by
    calc
      U.symm.conjAlgEquiv ℂ (J.tau x) =
          U.symm.conjAlgEquiv ℂ (S.conjAlgEquiv ℂ (star x)) := by
            rw [J.tau_eq_automorphism_star, ← hSconj]
      _ = U.conjAlgEquiv ℂ (star x) := hcancel (star x)
      _ = (adjointLinearEquiv U).conjAlgEquiv ℂ (star x) := by rw [hUadj]
      _ = star (U.symm.conjAlgEquiv ℂ x) :=
        (star_conjAlgEquiv_apply U.symm x).symm
  exact ⟨U.symm.conjAlgEquiv ℂ, hintertwine⟩

end FullMatrixInvolutionData

end
end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms FullMatrixInvolutionData.automorphism
#audit_axioms FullMatrixInvolutionData.exists_intertwiningAlgEquiv
