import GroupApproximation.Analysis.CStarCompletelyPositiveStar

/-!
# Completely positive maps are `⋆`-preserving, at an arbitrary C⋆-target

`Analysis.CStarCompletelyPositiveStar` proves that a completely positive map
is selfadjointness-preserving and `⋆`-preserving **for maps into `B(H)`**,
because that is the target the Stinespring chain needs.  Nothing in those
three proofs uses the target beyond the two facts that `star P * P` is
selfadjoint entrywise and that scalars commute with `star` the way they do in
any `⋆`-algebra, so the same argument runs verbatim at an arbitrary
`NonUnitalCStarAlgebra` target.  The order-zero layer needs exactly that
generality: an order-zero map lands in the C⋆-algebra `B`, not in a concrete
`B(H)`, and the very first thing one wants of it is that it preserves
adjoints.

The three statements are re-proved rather than the originals generalized: the
originals are cited by name in compiled modules and their binder lists are
pinned by `metadata/NON_MF_CLAIM_SIGNATURES.md`, so widening them in place
would move a pinned signature (see the repository note on signature pins).
The names here are deliberately *not* in the `IsCompletelyPositive` namespace
--- dot notation on a hypothesis `hφ : CStarExactness.IsCompletelyPositive φ`
resolves into `CStarExactness.IsCompletelyPositive`, and having two candidates
for `hφ.map_star` differing only in the target would be a trap.

Polarization (`CStarExactness.selfadjoint_eq_smul_sub_star_mul_self`) is
target-free already and is reused, not restated.
-/

namespace GroupApproximation
namespace OrderZero

open CStarExactness

universe u v

variable {A : Type u} [CStarAlgebra A] {B : Type v} [NonUnitalCStarAlgebra B]

/-- The `1 × 1` instance of complete positivity, at an arbitrary C⋆-target:
`φ (a⋆a)` is an entry of a matrix of the form `star P * P`, hence a sum of
elements `star b * b`, hence selfadjoint. -/
theorem isSelfAdjoint_map_star_mul_self_of_cp {φ : A →ₗ[ℂ] B}
    (hφ : IsCompletelyPositive φ) (a : A) :
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

/-- Completely positive maps carry selfadjoint elements to selfadjoint
elements, at an arbitrary C⋆-target. -/
theorem isSelfAdjoint_map_of_cp {φ : A →ₗ[ℂ] B}
    (hφ : IsCompletelyPositive φ) {h : A} (hh : IsSelfAdjoint h) :
    IsSelfAdjoint (φ h) := by
  rw [selfadjoint_eq_smul_sub_star_mul_self hh, map_sub, map_smul, map_smul]
  have hs1 := isSelfAdjoint_map_star_mul_self_of_cp hφ (h + 1)
  have hs2 := isSelfAdjoint_map_star_mul_self_of_cp hφ (h - 1)
  have hreal : ((4 : ℂ)⁻¹) = star ((4 : ℂ)⁻¹) := by
    rw [Complex.star_def, map_inv₀, map_ofNat]
  refine IsSelfAdjoint.sub ?_ ?_
  · show IsSelfAdjoint (((4 : ℂ)⁻¹) • φ (star (h + 1) * (h + 1)))
    rw [IsSelfAdjoint, star_smul, ← hreal, hs1.star_eq]
  · show IsSelfAdjoint (((4 : ℂ)⁻¹) • φ (star (h - 1) * (h - 1)))
    rw [IsSelfAdjoint, star_smul, ← hreal, hs2.star_eq]

/-- **Completely positive maps are `⋆`-preserving**, at an arbitrary
C⋆-target: `φ (x⋆) = (φ x)⋆`, by splitting `x` into real and imaginary
parts. -/
theorem map_star_of_cp {φ : A →ₗ[ℂ] B} (hφ : IsCompletelyPositive φ) (x : A) :
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
    (isSelfAdjoint_map_of_cp hφ hre_sa).star_eq,
    map_smul, map_smul, star_smul, Complex.star_def, Complex.conj_I,
    (isSelfAdjoint_map_of_cp hφ him_sa).star_eq, neg_smul, ← sub_eq_add_neg]

end OrderZero
end GroupApproximation
