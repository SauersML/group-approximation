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

/-- The transported Gram operation has the same zero-detection property as
the original C-star Gram operation.  This uses only injectivity of the
algebra equivalence, not preservation of the target positive cone. -/
theorem transportedInvolution_mul_self_eq_zero_iff
    {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
    (e : D ≃ₐ[ℂ] B) (x : B) :
    transportedInvolution e x * x = 0 ↔ x = 0 := by
  constructor
  · intro hzero
    have himage : e (star (e.symm x) * e.symm x) = 0 := by
      rw [← transportedInvolution_mul_self_eq_map_star_mul_self]
      exact hzero
    have hsource : star (e.symm x) * e.symm x = 0 := by
      apply e.injective
      simpa using himage
    have hxsource : e.symm x = 0 :=
      (CStarRing.star_mul_self_eq_zero_iff (e.symm x)).mp hsource
    calc
      x = e (e.symm x) := (e.apply_symm_apply x).symm
      _ = e 0 := congrArg e hxsource
      _ = 0 := map_zero e
  · rintro rfl
    simp

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
the original conjugator to be scalar.  This is the exact relation supplied
by the center theorem for an endomorphism algebra. -/
theorem exists_scalar_adjointInverse_trans_conjugator
    {D V : Type*} [CStarAlgebra D] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
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
unit-scalar relation between the conjugator and its adjoint. -/
theorem conjugator_eq_smul_adjoint_of_adjointInverse_trans_eq_smul_refl
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V ≃ₗ[ℂ] V) (α : ℂˣ)
    (hscalar :
      (adjointLinearEquiv T.symm).trans T =
        α • (LinearEquiv.refl ℂ V)) :
    T = α • adjointLinearEquiv T := by
  ext x
  have hx := DFunLike.congr_fun hscalar (adjointLinearEquiv T x)
  have hinv :
      adjointLinearEquiv T.symm (adjointLinearEquiv T x) = x := by
    simpa only [adjointLinearEquiv_symm] using
      (adjointLinearEquiv T).symm_apply_apply x
  change T (adjointLinearEquiv T.symm (adjointLinearEquiv T x)) =
    (α • (LinearEquiv.refl ℂ V)) (adjointLinearEquiv T x) at hx
  rw [hinv] at hx
  simpa using hx

/-- Every Skolem--Noether conjugator for the transported involution is a
unit scalar multiple of its adjoint. -/
theorem exists_scalar_conjugator_eq_smul_adjoint
    {D V : Type*} [CStarAlgebra D] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (e : D ≃ₐ[ℂ] Module.End ℂ V) (T : V ≃ₗ[ℂ] V)
    (hT : T.conjAlgEquiv ℂ = transportedInvolutionAutomorphism e) :
    ∃ α : ℂˣ, T = α • adjointLinearEquiv T := by
  obtain ⟨α, hα⟩ := exists_scalar_adjointInverse_trans_conjugator e T hT
  exact ⟨α,
    conjugator_eq_smul_adjoint_of_adjointInverse_trans_eq_smul_refl T α hα⟩

/-- If an invertible operator is a unit scalar multiple of its adjoint, then
that scalar times its conjugate is one. -/
theorem unitScalar_star_mul_self_eq_one_of_eq_smul_adjoint
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V]
    (T : V ≃ₗ[ℂ] V) (α : ℂˣ)
    (hT : T = α • adjointLinearEquiv T) :
    star (α : ℂ) * (α : ℂ) = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hTx : T x ≠ 0 := by
    intro hzero
    apply hx
    exact T.injective (by simpa using hzero)
  have hpoint (y : V) :
      T y = (α : ℂ) • T.toLinearMap.adjoint y := by
    simpa using DFunLike.congr_fun hT y
  have hinner :
      inner ℂ (T x) (T x) =
        (star (α : ℂ) * (α : ℂ)) * inner ℂ (T x) (T x) := by
    calc
      inner ℂ (T x) (T x) =
          inner ℂ ((α : ℂ) • T.toLinearMap.adjoint x) (T x) := by
        rw [hpoint]
      _ = star (α : ℂ) * inner ℂ (T.toLinearMap.adjoint x) (T x) := by
        rw [inner_smul_left]
      _ = star (α : ℂ) * inner ℂ x (T (T x)) := by
        rw [LinearMap.adjoint_inner_left]
      _ = star (α : ℂ) *
          inner ℂ x ((α : ℂ) • T.toLinearMap.adjoint (T x)) := by
        rw [hpoint]
      _ = star (α : ℂ) *
          ((α : ℂ) * inner ℂ x (T.toLinearMap.adjoint (T x))) := by
        rw [inner_smul_right]
      _ = (star (α : ℂ) * (α : ℂ)) * inner ℂ (T x) (T x) := by
        rw [LinearMap.adjoint_inner_right]
        ring
  have hinner_ne : inner ℂ (T x) (T x) ≠ 0 := by
    intro hzero
    exact hTx (inner_self_eq_zero.mp hzero)
  refine mul_right_cancel₀ hinner_ne ?_
  simpa using hinner.symm

/-- The unit scalar relating an invertible operator to its adjoint has
complex norm one. -/
theorem norm_unitScalar_eq_one_of_eq_smul_adjoint
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V]
    (T : V ≃ₗ[ℂ] V) (α : ℂˣ)
    (hT : T = α • adjointLinearEquiv T) :
    ‖(α : ℂ)‖ = 1 := by
  have hstar := unitScalar_star_mul_self_eq_one_of_eq_smul_adjoint T α hT
  have hnorm := congrArg norm hstar
  rw [norm_mul, norm_star, norm_one] at hnorm
  nlinarith [norm_nonneg (α : ℂ)]

/-- The scalar supplied by the transported-involution argument is an actual
unit-modulus phase. -/
theorem exists_phase_conjugator_eq_smul_adjoint
    {D V : Type*} [CStarAlgebra D] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (e : D ≃ₐ[ℂ] Module.End ℂ V) (T : V ≃ₗ[ℂ] V)
    (hT : T.conjAlgEquiv ℂ = transportedInvolutionAutomorphism e) :
    ∃ α : ℂˣ, ‖(α : ℂ)‖ = 1 ∧ T = α • adjointLinearEquiv T := by
  obtain ⟨α, hα⟩ := exists_scalar_conjugator_eq_smul_adjoint e T hT
  exact ⟨α, norm_unitScalar_eq_one_of_eq_smul_adjoint T α hα, hα⟩

/-- A complex unit satisfying `α̅α = 1` admits an explicit phase
correction `β` with `βα = β̅`.  The construction uses `β = i` when
`α = -1`, and `β = 1 + α̅` otherwise. -/
theorem exists_unitScalar_mul_eq_star
    (α : ℂˣ) (hα : star (α : ℂ) * (α : ℂ) = 1) :
    ∃ β : ℂˣ, (β : ℂ) * (α : ℂ) = star (β : ℂ) := by
  by_cases hminus : (α : ℂ) = -1
  · let β : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero
    refine ⟨β, ?_⟩
    simp [β, hminus]
  · have hnonzero : 1 + star (α : ℂ) ≠ 0 := by
      intro hzero
      have hstarzero : 1 + (α : ℂ) = 0 := by
        simpa using congrArg star hzero
      apply hminus
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hstarzero
    let β : ℂˣ := Units.mk0 (1 + star (α : ℂ)) hnonzero
    refine ⟨β, ?_⟩
    change (1 + star (α : ℂ)) * (α : ℂ) =
      star (1 + star (α : ℂ))
    calc
      (1 + star (α : ℂ)) * (α : ℂ) =
          (α : ℂ) + star (α : ℂ) * (α : ℂ) := by ring
      _ = (α : ℂ) + 1 := by rw [hα]
      _ = star (1 + star (α : ℂ)) := by simp [add_comm]

/-- The adjoint of a unit-scaled invertible operator is obtained by scaling
the adjoint by the conjugate unit. -/
theorem adjointLinearEquiv_unit_smul_apply
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    (T : V ≃ₗ[ℂ] V) (β : ℂˣ) (x : V) :
    adjointLinearEquiv (β • T) x =
      star (β : ℂ) • adjointLinearEquiv T x := by
  apply ext_inner_right ℂ
  intro y
  calc
    inner ℂ (adjointLinearEquiv (β • T) x) y =
        inner ℂ x ((β • T) y) := by
      exact LinearMap.adjoint_inner_left (β • T).toLinearMap y x
    _ = inner ℂ x ((β : ℂ) • T y) := by rfl
    _ = (β : ℂ) * inner ℂ x (T y) := by rw [inner_smul_right]
    _ = (β : ℂ) * inner ℂ (adjointLinearEquiv T x) y := by
      rw [LinearMap.adjoint_inner_left]
    _ = inner ℂ (star (β : ℂ) • adjointLinearEquiv T x) y := by
      rw [inner_smul_left, star_star]

/-- A scalar correction satisfying `βα = β̅` turns an
`α`-self-adjoint conjugator into a genuinely self-adjoint one. -/
theorem adjointLinearEquiv_unit_smul_eq_self
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    (T : V ≃ₗ[ℂ] V) (α β : ℂˣ)
    (hT : T = α • adjointLinearEquiv T)
    (hβ : (β : ℂ) * (α : ℂ) = star (β : ℂ)) :
    adjointLinearEquiv (β • T) = β • T := by
  ext x
  have hpoint : T x = (α : ℂ) • adjointLinearEquiv T x := by
    simpa using DFunLike.congr_fun hT x
  rw [adjointLinearEquiv_unit_smul_apply]
  calc
    star (β : ℂ) • adjointLinearEquiv T x =
        ((β : ℂ) * (α : ℂ)) • adjointLinearEquiv T x := by rw [hβ]
    _ = (β : ℂ) • ((α : ℂ) • adjointLinearEquiv T x) := by
      rw [smul_smul]
    _ = (β : ℂ) • T x := by rw [← hpoint]
    _ = (β • T) x := by rfl

/-- Rescaling a conjugator by a complex unit does not change the induced
inner automorphism. -/
theorem unit_smul_conjAlgEquiv_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V]
    (T : V ≃ₗ[ℂ] V) (β : ℂˣ) :
    (β • T).conjAlgEquiv ℂ = T.conjAlgEquiv ℂ := by
  exact LinearEquiv.conjAlgEquiv_ext_iff' (β • T) T |>.mpr ⟨β, rfl⟩

/-- The Skolem--Noether conjugator of a transported C-star involution can be
rescaled by a complex unit to become self-adjoint. -/
theorem exists_selfAdjoint_rescaling_of_transportedInvolution
    {D V : Type*} [CStarAlgebra D] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (e : D ≃ₐ[ℂ] Module.End ℂ V) (T : V ≃ₗ[ℂ] V)
    (hT : T.conjAlgEquiv ℂ = transportedInvolutionAutomorphism e) :
    ∃ β : ℂˣ, adjointLinearEquiv (β • T) = β • T := by
  obtain ⟨α, hα⟩ := exists_scalar_conjugator_eq_smul_adjoint e T hT
  have hunit := unitScalar_star_mul_self_eq_one_of_eq_smul_adjoint T α hα
  obtain ⟨β, hβ⟩ := exists_unitScalar_mul_eq_star α hunit
  exact ⟨β, adjointLinearEquiv_unit_smul_eq_self T α β hα hβ⟩

/-- The transported involution is implemented by a genuinely self-adjoint
conjugator, obtained by an explicit unit-scalar rescaling of the
Skolem--Noether conjugator. -/
theorem exists_selfAdjoint_conjugator_for_transportedInvolution
    {D V : Type*} [CStarAlgebra D] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (e : D ≃ₐ[ℂ] Module.End ℂ V) :
    ∃ S : V ≃ₗ[ℂ] V,
      S.conjAlgEquiv ℂ = transportedInvolutionAutomorphism e ∧
      adjointLinearEquiv S = S := by
  obtain ⟨T, hT⟩ := exists_conjugatingLinearEquiv_for_transportedInvolution e
  obtain ⟨β, hself⟩ := exists_selfAdjoint_rescaling_of_transportedInvolution e T hT
  refine ⟨β • T, ?_, hself⟩
  rw [unit_smul_conjAlgEquiv_eq, hT]

/-! ## Algebraic anisotropy of the corrected conjugator -/

/-- The rank-one endomorphism `v ↦ ⟨z,v⟩ w`, expressed through
Mathlib's inner-product linear maps. -/
def innerRankOneEnd
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (w z : V) : Module.End ℂ V :=
  (InnerProductSpace.toSpanSingleton ℂ V w).comp (innerₛₗ ℂ z)

@[simp] theorem innerRankOneEnd_apply
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (w z v : V) :
    innerRankOneEnd w z v = inner ℂ z v • w := by
  simp [innerRankOneEnd]

@[simp] theorem star_innerRankOneEnd
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (w z : V) :
    star (innerRankOneEnd w z) = innerRankOneEnd z w := by
  rw [LinearMap.star_eq_adjoint, innerRankOneEnd, LinearMap.adjoint_comp,
    LinearMap.adjoint_innerₛₗ_apply, LinearMap.adjoint_toSpanSingleton]

/-- Any conjugator implementing a transported C-star involution has no
nonzero isotropic vector for the inverse-conjugator form.  Otherwise the
rank-one operator with range spanned by that vector would have zero
transported Gram element, contradicting C-star cancellation in the source. -/
theorem conjugator_inverseForm_anisotropic
    {D V : Type*} [CStarAlgebra D] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (e : D ≃ₐ[ℂ] Module.End ℂ V) (S : V ≃ₗ[ℂ] V)
    (hS : S.conjAlgEquiv ℂ = transportedInvolutionAutomorphism e)
    {w : V} (hw : w ≠ 0) :
    inner ℂ w (S.symm w) ≠ 0 := by
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
      transportedInvolution e x = S.conjAlgEquiv ℂ (star x) := by
    rw [transportedInvolution_eq_automorphism_star, ← hS]
  have hGram : transportedInvolution e A * A = 0 := by
    ext v
    rw [Module.End.mul_apply, htransport]
    simp [LinearEquiv.conjAlgEquiv_apply, A, hisotropic]
  exact hAne ((transportedInvolution_mul_self_eq_zero_iff e A).mp hGram)

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
#audit_axioms transportedInvolution_mul_self_eq_zero_iff
#audit_axioms transportedInvolutionAutomorphism
#audit_axioms transportedInvolution_eq_automorphism_star
#audit_axioms exists_conjugatingLinearEquiv_for_transportedInvolution
#audit_axioms exists_scalar_adjointInverse_trans_conjugator
#audit_axioms conjugator_eq_smul_adjoint_of_adjointInverse_trans_eq_smul_refl
#audit_axioms exists_scalar_conjugator_eq_smul_adjoint
#audit_axioms unitScalar_star_mul_self_eq_one_of_eq_smul_adjoint
#audit_axioms norm_unitScalar_eq_one_of_eq_smul_adjoint
#audit_axioms exists_phase_conjugator_eq_smul_adjoint
#audit_axioms exists_unitScalar_mul_eq_star
#audit_axioms adjointLinearEquiv_unit_smul_apply
#audit_axioms adjointLinearEquiv_unit_smul_eq_self
#audit_axioms unit_smul_conjAlgEquiv_eq
#audit_axioms exists_selfAdjoint_rescaling_of_transportedInvolution
#audit_axioms exists_selfAdjoint_conjugator_for_transportedInvolution
#audit_axioms innerRankOneEnd
#audit_axioms star_innerRankOneEnd
#audit_axioms conjugator_inverseForm_anisotropic
#audit_axioms exists_conjugatingLinearEquiv_formula_for_transportedInvolution
