import GroupApproximation.Analysis.CStarCompletelyPositiveForm

/-!
# Completely positive maps are star-preserving

## What this module proves

For a completely positive `φ : A →ₗ[ℂ] (H →L[ℂ] H)` on a **unital**
C⋆-algebra:

* `IsCompletelyPositive.isSelfAdjoint_map_star_mul_self` -- `φ (a⋆a)` is
  selfadjoint, directly from the `1 × 1` instance of complete positivity:
  the image is `p⋆p` for an operator `p`;
* `selfadjoint_eq_smul_sub_star_mul_self` -- the polarization
  `4h = (h+1)⋆(h+1) - (h-1)⋆(h-1)` writes every selfadjoint element as a
  real combination of elements of the form `a⋆a`;
* `IsCompletelyPositive.map_star` -- hence `φ (x⋆) = (φ x)⋆`: split `x`
  into real and imaginary parts, each mapped to a selfadjoint operator.

Star-preservation is the conjugate-symmetry input of the Stinespring form:
without it the sesquilinear form of `CStarCompletelyPositiveForm` would not
define a pre-inner-product.  Everything here is order-free, in the house
spelling.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `RE.05` remains
**MISSING**.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace

universe u w

variable {A : Type u} [CStarAlgebra A]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The `1 × 1` instance of complete positivity: `φ (a⋆a)` is of the form
`p⋆p`, hence selfadjoint. -/
theorem IsCompletelyPositive.isSelfAdjoint_map_star_mul_self
    {φ : A →ₗ[ℂ] (H →L[ℂ] H)} (hφ : IsCompletelyPositive φ) (a : A) :
    IsSelfAdjoint (φ (star a * a)) := by
  obtain ⟨N, hN⟩ := star_col_mul_col (n := 1) ![a]
  obtain ⟨P, hP⟩ :=
    hφ 1 (CStarMatrix.ofMatrix (Matrix.of fun i j => star (![a] i) * ![a] j))
      ⟨N, hN⟩
  have hentry : φ (star a * a) = (star P * P) 0 0 := by
    have h := congrArg (fun M => M (0 : Fin 1) (0 : Fin 1)) hP
    simpa using h
  rw [hentry, cstarMatrix_mul_apply]
  have hterm : ∀ k : Fin 1, IsSelfAdjoint ((star P) 0 k * P k 0) := by
    intro k
    rw [cstarMatrix_star_apply]
    exact IsSelfAdjoint.star_mul_self (P k 0)
  rw [Fin.sum_univ_one]
  exact hterm 0

/-- **Polarization**: every selfadjoint element of a unital ⋆-algebra is a
real combination of elements of the form `a⋆a`:
`4h = (h+1)⋆(h+1) - (h-1)⋆(h-1)`. -/
theorem selfadjoint_eq_smul_sub_star_mul_self {h : A}
    (hh : IsSelfAdjoint h) :
    h = ((4 : ℂ)⁻¹) • (star (h + 1) * (h + 1))
        - ((4 : ℂ)⁻¹) • (star (h - 1) * (h - 1)) := by
  have h1 : star (h + 1) = h + 1 := by
    rw [star_add, hh.star_eq, star_one]
  have h2 : star (h - 1) = h - 1 := by
    rw [star_sub, hh.star_eq, star_one]
  rw [h1, h2, ← smul_sub]
  have hexp : (h + 1) * (h + 1) - (h - 1) * (h - 1) = (4 : ℂ) • h := by
    have : (h + 1) * (h + 1) - (h - 1) * (h - 1)
        = h * h + h + h + 1 - (h * h - h - h + 1) := by
      congr 1
      · rw [add_mul, mul_add, mul_add, mul_one, one_mul, one_mul]
        abel
      · rw [sub_mul, mul_sub, mul_sub, mul_one, one_mul, one_mul]
        abel
    rw [this]
    have h4 : h * h + h + h + 1 - (h * h - h - h + 1)
        = h + h + (h + h) := by abel
    rw [h4]
    have : ((4 : ℂ)) • h = ((2 : ℂ)) • h + ((2 : ℂ)) • h := by
      rw [← add_smul]
      norm_num
    rw [this]
    have h2h : ((2 : ℂ)) • h = h + h := by
      rw [show ((2 : ℂ)) = 1 + 1 by norm_num, add_smul, one_smul]
    rw [h2h]
  rw [hexp, smul_smul]
  norm_num

/-- Completely positive maps carry selfadjoint elements to selfadjoint
operators. -/
theorem IsCompletelyPositive.isSelfAdjoint_map
    {φ : A →ₗ[ℂ] (H →L[ℂ] H)} (hφ : IsCompletelyPositive φ) {h : A}
    (hh : IsSelfAdjoint h) : IsSelfAdjoint (φ h) := by
  rw [selfadjoint_eq_smul_sub_star_mul_self hh, map_sub, map_smul, map_smul]
  have hs1 := hφ.isSelfAdjoint_map_star_mul_self (h + 1)
  have hs2 := hφ.isSelfAdjoint_map_star_mul_self (h - 1)
  have hreal : ((4 : ℂ)⁻¹) = star ((4 : ℂ)⁻¹) := by
    rw [Complex.star_def, map_inv₀, map_ofNat]
  refine IsSelfAdjoint.sub ?_ ?_
  · show IsSelfAdjoint (((4 : ℂ)⁻¹) • φ (star (h + 1) * (h + 1)))
    rw [IsSelfAdjoint, star_smul, ← hreal, hs1.star_eq]
  · show IsSelfAdjoint (((4 : ℂ)⁻¹) • φ (star (h - 1) * (h - 1)))
    rw [IsSelfAdjoint, star_smul, ← hreal, hs2.star_eq]

/-- **Completely positive maps are star-preserving**:
`φ (x⋆) = (φ x)⋆`, by splitting into real and imaginary parts. -/
theorem IsCompletelyPositive.map_star
    {φ : A →ₗ[ℂ] (H →L[ℂ] H)} (hφ : IsCompletelyPositive φ) (x : A) :
    φ (star x) = star (φ x) := by
  set hre : A := ((2 : ℂ)⁻¹) • (x + star x) with hre_def
  set him : A := (((2 : ℂ) * Complex.I)⁻¹) • (x - star x) with him_def
  have hre_sa : IsSelfAdjoint hre := by
    rw [hre_def, IsSelfAdjoint, star_smul, star_add, star_star,
      Complex.star_def]
    rw [show (starRingEnd ℂ) ((2 : ℂ)⁻¹) = ((2 : ℂ)⁻¹) by
      rw [map_inv₀, map_ofNat]]
    rw [add_comm]
  have him_sa : IsSelfAdjoint him := by
    rw [him_def, IsSelfAdjoint, star_smul, star_sub, star_star,
      Complex.star_def]
    rw [show (starRingEnd ℂ) (((2 : ℂ) * Complex.I)⁻¹)
        = -(((2 : ℂ) * Complex.I)⁻¹) by
      rw [map_inv₀, map_mul, Complex.conj_I]
      rw [show (starRingEnd ℂ) (2 : ℂ) = 2 from map_ofNat _ 2]
      rw [show (2 : ℂ) * -Complex.I = -(2 * Complex.I) by ring]
      rw [inv_neg]]
    rw [neg_smul, ← smul_neg, neg_sub]
  have hx : x = hre + Complex.I • him := by
    rw [hre_def, him_def, smul_smul]
    have hI : Complex.I * ((2 : ℂ) * Complex.I)⁻¹ = -((2 : ℂ))⁻¹ * (-1) := by
      rw [mul_inv, ← mul_assoc]
      rw [show Complex.I * ((2:ℂ))⁻¹ * (Complex.I)⁻¹
          = ((2:ℂ))⁻¹ * (Complex.I * (Complex.I)⁻¹) by ring]
      rw [mul_inv_cancel₀ Complex.I_ne_zero, mul_one]
      ring
    rw [hI]
    rw [show (-((2:ℂ))⁻¹ * (-1)) = ((2:ℂ))⁻¹ by ring]
    rw [← smul_add]
    rw [show x + star x + (x - star x) = x + x by abel]
    rw [show ((2 : ℂ))⁻¹ • (x + x) = ((2 : ℂ))⁻¹ • (((2 : ℂ)) • x) by
      rw [show ((2 : ℂ)) • x = x + x by
        rw [show ((2:ℂ)) = 1 + 1 by norm_num, add_smul, one_smul]]]
    rw [smul_smul]
    norm_num
  have hstar : star x = hre - Complex.I • him := by
    rw [hx, star_add, hre_sa.star_eq, star_smul, him_sa.star_eq,
      Complex.star_def, Complex.conj_I, neg_smul, ← sub_eq_add_neg]
  rw [hstar, hx, map_sub, map_add, star_add,
    (hφ.isSelfAdjoint_map hre_sa).star_eq,
    map_smul, star_smul, Complex.star_def, Complex.conj_I,
    (hφ.isSelfAdjoint_map him_sa).star_eq, neg_smul, ← sub_eq_add_neg]

end CStarExactness
end GroupApproximation
