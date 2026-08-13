import GroupApproximation.Sofic.LiteralNonMFPresentation

/-!
# Intrinsic relations in the literal six-generator base

This module exposes the twenty defining relators as equalities in the
presented group itself.  These are presentation-theoretic statements: no
matrix realization, completeness theorem, or equality reflected from a
quotient is used.
-/

namespace GroupApproximation
namespace LiteralBaseRelations

open LiteralNonMFPresentation
open scoped commutatorElement

noncomputable section

abbrev baseWord : FreeGroup BaseGenerator →* Base :=
  PresentedGroup.mk (baseRelators : Set (FreeGroup BaseGenerator))

abbrev v1 : Base := PresentedGroup.of v1Index
abbrev v2 : Base := PresentedGroup.of v2Index
abbrev v3 : Base := PresentedGroup.of v3Index
abbrev x : Base := PresentedGroup.of xIndex
abbrev y : Base := PresentedGroup.of yIndex
abbrev z : Base := PresentedGroup.of zIndex

@[simp] theorem baseWord_of (i : BaseGenerator) :
    baseWord (FreeGroup.of i) = PresentedGroup.of i := rfl

/-- Every one of the twenty displayed relators is the identity in the
literal presented base. -/
theorem baseRelator_eq_one {r : FreeGroup BaseGenerator}
    (hr : r ∈ baseRelators) : baseWord r = 1 :=
  PresentedGroup.one_of_mem (Finset.mem_coe.mpr hr)

@[simp] theorem x_cube : x ^ 3 = 1 := by
  simpa only [baseRelXCube, map_pow, baseWord_of] using
    baseRelator_eq_one (show baseRelXCube ∈ baseRelators by simp [baseRelators])

@[simp] theorem y_cube : y ^ 3 = 1 := by
  simpa only [baseRelYCube, map_pow, baseWord_of] using
    baseRelator_eq_one (show baseRelYCube ∈ baseRelators by simp [baseRelators])

@[simp] theorem z_sq : z ^ 2 = 1 := by
  simpa only [baseRelZSq, map_pow, baseWord_of] using
    baseRelator_eq_one (show baseRelZSq ∈ baseRelators by simp [baseRelators])

@[simp] theorem xz_cube : (x * z) ^ 3 = 1 := by
  simpa only [baseRelXZCube, map_pow, map_mul, baseWord_of] using
    baseRelator_eq_one
      (show baseRelXZCube ∈ baseRelators by simp [baseRelators])

@[simp] theorem yz_cube : (y * z) ^ 3 = 1 := by
  simpa only [baseRelYZCube, map_pow, map_mul, baseWord_of] using
    baseRelator_eq_one
      (show baseRelYZCube ∈ baseRelators by simp [baseRelators])

@[simp] theorem x_inv_z_x_y_sq : (x⁻¹ * z * x * y) ^ 2 = 1 := by
  simpa only [baseRelXInvZXY, map_pow, map_mul, map_inv, baseWord_of] using
    baseRelator_eq_one
      (show baseRelXInvZXY ∈ baseRelators by simp [baseRelators])

@[simp] theorem y_inv_z_y_x_sq : (y⁻¹ * z * y * x) ^ 2 = 1 := by
  simpa only [baseRelYInvZYX, map_pow, map_mul, map_inv, baseWord_of] using
    baseRelator_eq_one
      (show baseRelYInvZYX ∈ baseRelators by simp [baseRelators])

@[simp] theorem xy_six : (x * y) ^ 6 = 1 := by
  simpa only [baseRelXYSix, map_pow, map_mul, baseWord_of] using
    baseRelator_eq_one
      (show baseRelXYSix ∈ baseRelators by simp [baseRelators])

theorem commute_v1_v2 : Commute v1 v2 := by
  have h : baseWord (commutatorWord bv1 bv2) = 1 :=
    baseRelator_eq_one (show baseRelV12 ∈ baseRelators by simp [baseRelators])
  rw [map_commutatorWord] at h
  exact commutatorElement_eq_one_iff_commute.mp h

theorem commute_v1_v3 : Commute v1 v3 := by
  have h : baseWord (commutatorWord bv1 bv3) = 1 :=
    baseRelator_eq_one (show baseRelV13 ∈ baseRelators by simp [baseRelators])
  rw [map_commutatorWord] at h
  exact commutatorElement_eq_one_iff_commute.mp h

theorem commute_v2_v3 : Commute v2 v3 := by
  have h : baseWord (commutatorWord bv2 bv3) = 1 :=
    baseRelator_eq_one (show baseRelV23 ∈ baseRelators by simp [baseRelators])
  rw [map_commutatorWord] at h
  exact commutatorElement_eq_one_iff_commute.mp h

theorem x_conj_v1 : x * v1 * x⁻¹ = v3 := by
  have h := baseRelator_eq_one
    (show baseRelXV1 ∈ baseRelators by simp [baseRelators])
  simpa only [baseRelXV1, map_mul, map_inv, baseWord_of] using
    (mul_inv_eq_one.mp h)

theorem x_conj_v2 : x * v2 * x⁻¹ = v1 := by
  have h := baseRelator_eq_one
    (show baseRelXV2 ∈ baseRelators by simp [baseRelators])
  simpa only [baseRelXV2, map_mul, map_inv, baseWord_of] using
    (mul_inv_eq_one.mp h)

theorem x_conj_v3 : x * v3 * x⁻¹ = v2 := by
  have h := baseRelator_eq_one
    (show baseRelXV3 ∈ baseRelators by simp [baseRelators])
  simpa only [baseRelXV3, map_mul, map_inv, baseWord_of] using
    (mul_inv_eq_one.mp h)

theorem y_conj_v1 : y * v1 * y⁻¹ = v1 := by
  have h := baseRelator_eq_one
    (show baseRelYV1 ∈ baseRelators by simp [baseRelators])
  simpa only [baseRelYV1, map_mul, map_inv, baseWord_of] using
    (mul_inv_eq_one.mp h)

theorem y_conj_v2 : y * v2 * y⁻¹ = v2⁻¹ * v3 := by
  have h := baseRelator_eq_one
    (show baseRelYV2 ∈ baseRelators by simp [baseRelators])
  simpa only [baseRelYV2, map_mul, map_inv, baseWord_of] using
    (mul_inv_eq_one.mp h)

theorem y_conj_v3 : y * v3 * y⁻¹ = v1 * v2⁻¹ := by
  have h := baseRelator_eq_one
    (show baseRelYV3 ∈ baseRelators by simp [baseRelators])
  simpa only [baseRelYV3, map_mul, map_inv, baseWord_of] using
    (mul_inv_eq_one.mp h)

theorem z_conj_v1 : z * v1 * z⁻¹ = v2 * v3⁻¹ := by
  have h := baseRelator_eq_one
    (show baseRelZV1 ∈ baseRelators by simp [baseRelators])
  simpa only [baseRelZV1, map_mul, map_inv, baseWord_of] using
    (mul_inv_eq_one.mp h)

theorem z_conj_v2 : z * v2 * z⁻¹ = v1 * v3⁻¹ := by
  have h := baseRelator_eq_one
    (show baseRelZV2 ∈ baseRelators by simp [baseRelators])
  simpa only [baseRelZV2, map_mul, map_inv, baseWord_of] using
    (mul_inv_eq_one.mp h)

theorem z_conj_v3 : z * v3 * z⁻¹ = v3⁻¹ := by
  have h := baseRelator_eq_one
    (show baseRelZV3 ∈ baseRelators by simp [baseRelators])
  simpa only [baseRelZV3, map_mul, map_inv, baseWord_of, inv_inv] using
    (mul_inv_eq_one.mp h)

end

end LiteralBaseRelations
end GroupApproximation
