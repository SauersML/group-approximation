import GroupApproximation.Monsters.ExplicitIntegralLinearModel
import GroupApproximation.Sofic.LiteralNonMFLinearWitness
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Group

/-!
# The vertical factor of the explicit witness is residually finite

The concrete witness `W = ClLamp(X) ⋊ V` sits in a short exact sequence whose
kernel is the locally finite Clifford lamp group and whose quotient is the
vertical factor `V = Telescope ⋊ ℤ`.  The kernel is operator-MF for soft
reasons; this file supplies the other half, with no external input: `V` is
residually finite, hence operator-MF.

The usual argument would quote Mal'cev — `V` is finitely generated linear over
`ℤ[1/2]`, therefore residually finite.  That needs a localized coefficient
ring.  The argument below avoids it.  Reduction of the *integral* model of the
affine base modulo an **odd** modulus `2k+1` is a homomorphism to a finite
group in which the compressing diagonal `D = diag(2,2,2,1)` is invertible,
because `det D = 8` is a unit there.  Conjugation by `D` therefore descends to
the finite quotient, so the reduction extends over the whole telescope and its
shift by the ascending-HNN universal property `verticalLift`.  Odd moduli
still separate every nonidentity integral matrix
(`exists_odd_modulus_reduction_ne_one`), and the `ℤ`-coordinate is separated
by its own cyclic quotient.
-/

namespace GroupApproximation
namespace WitnessVertical

open Matrix ExplicitLinearModel ExplicitIntegralLinearModel
open MarkedCompression MappingTelescope
open LiteralNonMFLinearWitness

/-! ## The integral realization of the affine base -/

/-- The integral matrix realizing an element of the concrete affine base. -/
noncomputable def redZ : gammaBar →* MatZˣ :=
  gammaInt.subtype.comp gammaIntEquivGammaBar.symm.toMonoidHom

theorem castGL_redZ (u : gammaBar) : castGL (redZ u) = (u : Matˣ) := by
  have h :
      ((gammaIntEquivGammaBar (gammaIntEquivGammaBar.symm u) : gammaBar) : Matˣ) =
        castGL ((gammaIntEquivGammaBar.symm u : gammaInt) : MatZˣ) := rfl
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem redZ_injective : Function.Injective redZ := by
  intro a b hab
  have h := congrArg castGL hab
  rw [castGL_redZ, castGL_redZ] at h
  exact Subtype.ext h

/-! ## Entrywise casting -/

/-- Entrywise casting of integral matrices to rational ones. -/
noncomputable def castMat : MatZ →+* Mat := (Int.castRingHom ℚ).mapMatrix

theorem castMat_injective : Function.Injective castMat := by
  intro a b hab
  ext i j
  have h := congrArg (fun M : Mat => M i j) hab
  simp only [castMat, RingHom.mapMatrix_apply, Matrix.map_apply,
    eq_intCast] at h
  exact_mod_cast h

theorem castMat_redZ (u : gammaBar) :
    castMat (redZ u : MatZ) = ((u : Matˣ) : Mat) := by
  have h := castGL_redZ u
  have h' := congrArg (fun w : Matˣ => (w : Mat)) h
  simpa [castMat, castGL, GeneralLinearGroup.map_apply,
    RingHom.mapMatrix_apply] using h'

/-! ## The compressing diagonal over an arbitrary ring -/

/-- The diagonal entries `2,2,2,1` of the compressing matrix. -/
def dDiagFun (R : Type*) [CommRing R] : Fin 4 → R
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 1

/-- The compressing diagonal `diag(2,2,2,1)` over any commutative ring. -/
def dDiag (R : Type*) [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  Matrix.diagonal (dDiagFun R)

theorem map_dDiag {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    f.mapMatrix (dDiag R) = dDiag S := by
  rw [dDiag, dDiag, RingHom.mapMatrix_apply,
    Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  fin_cases i <;> simp [dDiagFun, map_ofNat]

theorem dDiag_rat : dDiag ℚ = dM := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dDiag, dM, dDiagFun, Matrix.diagonal]

theorem det_dDiag (R : Type*) [CommRing R] : (dDiag R).det = 8 := by
  rw [dDiag, Matrix.det_diagonal, Fin.prod_univ_four]
  simp only [dDiagFun]
  norm_num

theorem isUnit_dDiag {R : Type*} [CommRing R] (h : IsUnit (2 : R)) :
    IsUnit (dDiag R) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_dDiag]
  have h8 : (8 : R) = 2 ^ 3 := by norm_num
  rw [h8]
  exact h.pow 3

/-- Two is invertible modulo every odd number. -/
theorem isUnit_two_zmod (k : ℕ) : IsUnit (2 : ZMod (2 * k + 1)) := by
  rw [isUnit_iff_exists_inv]
  refine ⟨(k : ZMod (2 * k + 1)) + 1, ?_⟩
  have hzero : ((2 * k + 1 : ℕ) : ZMod (2 * k + 1)) = 0 := ZMod.natCast_self _
  push_cast at hzero ⊢
  linear_combination hzero

/-! ## Congruence quotients compatible with the compression -/

instance neZeroOdd (k : ℕ) : NeZero (2 * k + 1) := ⟨by omega⟩

/-- Reduction of the affine base modulo the odd number `2k+1`. -/
noncomputable def redMod (k : ℕ) :
    gammaBar →* GeneralLinearGroup (Fin 4) (ZMod (2 * k + 1)) :=
  (integralGLReduction (Fin 4) (2 * k + 1)).comp redZ

/-- The compressing diagonal modulo `2k+1`, as an invertible matrix. -/
noncomputable def dMod (k : ℕ) :
    GeneralLinearGroup (Fin 4) (ZMod (2 * k + 1)) :=
  (isUnit_dDiag (isUnit_two_zmod k)).unit

@[simp] theorem coe_dMod (k : ℕ) :
    ((dMod k : GeneralLinearGroup (Fin 4) (ZMod (2 * k + 1))) :
      Matrix (Fin 4) (Fin 4) (ZMod (2 * k + 1))) = dDiag _ :=
  IsUnit.unit_spec _

@[simp] theorem coe_redMod (k : ℕ) (u : gammaBar) :
    ((redMod k u : GeneralLinearGroup (Fin 4) (ZMod (2 * k + 1))) :
      Matrix (Fin 4) (Fin 4) (ZMod (2 * k + 1))) =
      (Int.castRingHom (ZMod (2 * k + 1))).mapMatrix (redZ u : MatZ) := rfl

/-- The compression is implemented over `ℤ` by right multiplication by the
compressing diagonal.  This is the only place the rational model is used. -/
theorem redZ_conjD_mul (u : gammaBar) :
    (redZ (conjD u) : MatZ) * dDiag ℤ = dDiag ℤ * (redZ u : MatZ) := by
  apply castMat_injective
  rw [map_mul, map_mul, castMat_redZ, castMat_redZ]
  show ((conjD u : gammaBar) : Matˣ) * castMat (dDiag ℤ) =
    castMat (dDiag ℤ) * ((u : Matˣ) : Mat)
  rw [show castMat (dDiag ℤ) = dM from (map_dDiag _).trans dDiag_rat]
  show (dU * (u : Matˣ) * dU⁻¹ : Matˣ) * dM = dM * ((u : Matˣ) : Mat)
  show dM * ((u : Matˣ) : Mat) * dInvM * dM = dM * ((u : Matˣ) : Mat)
  rw [mul_assoc (dM * ((u : Matˣ) : Mat)), dM_inv', mul_one]

theorem redMod_conjD_mul (k : ℕ) (u : gammaBar) :
    redMod k (conjD u) * dMod k = dMod k * redMod k u := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_dMod, coe_redMod, coe_redMod,
    ← map_dDiag (Int.castRingHom (ZMod (2 * k + 1))), ← map_mul, ← map_mul,
    redZ_conjD_mul]

theorem redMod_conjD (k : ℕ) (u : gammaBar) :
    redMod k (conjD u) = dMod k * redMod k u * (dMod k)⁻¹ := by
  rw [← redMod_conjD_mul, mul_inv_cancel_right]

/-! ## Finite quotients of the vertical factor -/

/-- The congruence quotient of the vertical factor modulo `2k+1`. -/
noncomputable def verticalMod (k : ℕ) :
    Vertical alpha conjD_injective →*
      GeneralLinearGroup (Fin 4) (ZMod (2 * k + 1)) :=
  verticalLift alpha conjD_injective (redMod k) (dMod k) (redMod_conjD k)

theorem verticalMod_inl_level (k n : ℕ) (x : gammaBar) :
    verticalMod k (SemidirectProduct.inl (level alpha conjD_injective n x)) =
      (dMod k ^ n)⁻¹ * redMod k x * dMod k ^ n :=
  verticalLift_inl_level alpha conjD_injective (redMod k) (dMod k)
    (redMod_conjD k) n x

/-! ## Residual finiteness -/

theorem redZ_ne_one {x : gammaBar} (hx : x ≠ 1) : redZ x ≠ 1 := by
  intro h
  exact hx (redZ_injective (h.trans (map_one redZ).symm))

/-- **The vertical factor of the explicit witness is residually finite.** -/
theorem vertical_residuallyFinite :
    Group.ResiduallyFinite (Vertical alpha conjD_injective) := by
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro v hv
  by_cases hr : v.right = 1
  · -- The telescope coordinate is nontrivial: use a congruence quotient.
    have hvl : v.left ≠ 1 := by
      intro h
      apply hv
      have hmul := SemidirectProduct.inl_left_mul_inr_right v
      rw [h, hr] at hmul
      simpa only [map_one, one_mul] using hmul.symm
    obtain ⟨⟨n, x⟩, hx⟩ := mk_surjective alpha conjD_injective v.left
    have hxne : x ≠ 1 := by
      intro h
      apply hvl
      rw [← hx, h]
      exact (map_one (level alpha conjD_injective n))
    obtain ⟨k, hk⟩ :=
      exists_odd_modulus_reduction_ne_one (Fin 4) (redZ_ne_one hxne)
    refine ⟨GeneralLinearGroup (Fin 4) (ZMod (2 * k + 1)), inferInstance,
      inferInstance, verticalMod k, ?_⟩
    have hv_eq : v = SemidirectProduct.inl (level alpha conjD_injective n x) := by
      have hmul := SemidirectProduct.inl_left_mul_inr_right v
      rw [hr] at hmul
      simp only [map_one, mul_one] at hmul
      rw [← hmul, ← hx]
      rfl
    rw [hv_eq, verticalMod_inl_level]
    intro hone
    apply hk
    have hx1 : redMod k x = 1 := by
      have h : dMod k ^ n *
          ((dMod k ^ n)⁻¹ * redMod k x * dMod k ^ n) * (dMod k ^ n)⁻¹ = 1 := by
        rw [hone]
        group
      calc redMod k x
          = dMod k ^ n *
              ((dMod k ^ n)⁻¹ * redMod k x * dMod k ^ n) * (dMod k ^ n)⁻¹ := by
            group
        _ = 1 := h
    simpa [redMod] using hx1
  · -- The integer coordinate is nontrivial: use its own cyclic quotient.
    set nz : ℤ := Multiplicative.toAdd v.right with hnz
    have hnz0 : nz ≠ 0 := by
      intro h
      apply hr
      have : v.right = Multiplicative.ofAdd nz := rfl
      rw [this, h]
      rfl
    have hm : NeZero (nz.natAbs + 1) := ⟨by omega⟩
    refine ⟨Multiplicative (ZMod (nz.natAbs + 1)), inferInstance, inferInstance,
      (AddMonoidHom.toMultiplicative
          (Int.castAddHom (ZMod (nz.natAbs + 1)))).comp
        SemidirectProduct.rightHom, ?_⟩
    intro hone
    have : (nz : ZMod (nz.natAbs + 1)) = 0 := by
      have h := congrArg Multiplicative.toAdd hone
      simpa [hnz] using h
    exact intCast_zmod_natAbs_add_one_ne_zero hnz0 this

/-- **The vertical factor of the explicit witness is operator-MF.**  This is
the quotient half of the extension-permanence failure: the kernel and the
quotient of the witness are both MF, while the witness itself is not. -/
theorem vertical_isOperatorMF : IsOperatorMF (Vertical alpha conjD_injective) := by
  letI := vertical_residuallyFinite
  exact isOperatorMF_of_residuallyFinite

end WitnessVertical
end GroupApproximation
