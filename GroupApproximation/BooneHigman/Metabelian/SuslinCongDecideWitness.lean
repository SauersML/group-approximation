import GroupApproximation.BooneHigman.Metabelian.SuslinCongDecideUnip
import GroupApproximation.Meta.AxiomGuard

/-!
# Deciding `SuslinCongVacIncl`, part 2: the explicit Krstić–McCool-type witness

Lane `bh-met-92i`.

For `q ∈ A` and `k ∈ ℕ` let (over `A[X]`)
`h_{q,k} = [[1 + q X^k, X^{3k}], [q³, 1 - q X^k + q² X^{2k}]]`
(`suslinCongDecide_kmMat`, `suslinCongDecide_km`).  Its determinant is `1`
(`suslinCongDecide_kmMat_det`).  This is the matrix family of Krstić–McCool ("Free quotients of
`SL₂(R[x])`", Proc. AMS 125 (1997)) as written out in Knudson (arXiv math/9803139), with the
integer `p` replaced by `q`.

The witness `σ_{q,k} = h_{q,k} · E₁₂(-X^{3k}) · E₂₁(-q³)` (`suslinCongDecide_wit`) satisfies, all
PROVED here:
* `det σ = 1` (`suslinCongDecide_wit_det`);
* `σ(0) = 1` for `k ≠ 0` (`suslinCongDecide_wit_const`), since `h(0) = E₂₁(q³)`;
* `σ ≡ 1 mod 𝔪^N` whenever `q ∈ 𝔪^N` (`suslinCongDecide_wit_mod`), since
  `h ≡ E₁₂(X^{3k}) mod q`.
For `k = 1` it is `[[1 + qX + q⁴X⁴, -qX⁴], [q⁴X - q⁵X² + q⁶X³, 1 - qX + q²X² - q³X³]]`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- The Krstić–McCool-type matrix `[[1 + q X^k, X^{3k}], [q³, 1 - q X^k + q² X^{2k}]]`. -/
noncomputable def suslinCongDecide_kmMat {A : Type*} [CommRing A] (q : A) (k : ℕ) :
    Matrix (Fin 2) (Fin 2) A[X] :=
  !![1 + C q * X ^ k, (X ^ k) ^ 3; C q ^ 3, 1 - C q * X ^ k + C q ^ 2 * (X ^ k) ^ 2]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongDecide_kmMat

/-- `det h_{q,k} = 1`. -/
theorem suslinCongDecide_kmMat_det {A : Type*} [CommRing A] (q : A) (k : ℕ) :
    Matrix.det (suslinCongDecide_kmMat q k) = 1 := by
  rw [suslinCongDecide_kmMat, Matrix.det_fin_two_of]
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongDecide_kmMat_det

/-- `h_{q,k}` as a unit. -/
noncomputable def suslinCongDecide_km {A : Type*} [CommRing A] (q : A) (k : ℕ) :
    (Matrix (Fin 2) (Fin 2) A[X])ˣ :=
  Matrix.SpecialLinearGroup.toGL ⟨suslinCongDecide_kmMat q k, suslinCongDecide_kmMat_det q k⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongDecide_km

/-- `det h_{q,k} = 1`, for the unit. -/
theorem suslinCongDecide_km_det {A : Type*} [CommRing A] (q : A) (k : ℕ) :
    Matrix.det (suslinCongDecide_km q k : Matrix (Fin 2) (Fin 2) A[X]) = 1 :=
  suslinCongDecide_kmMat_det q k

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongDecide_km_det

/-- Modulo `q`: `h_{q,k} ↦ E₁₂(X^{3k})`. -/
theorem suslinCongDecide_map_km_of_C {A S : Type*} [CommRing A] [CommRing S] (f : A[X] →+* S)
    {q : A} (hq : f (C q) = 0) (k : ℕ) :
    elementaryMatrixUnitMap (ι := Fin 2) f (suslinCongDecide_km q k) =
      elementaryUnit (0 : Fin 2) 1 (by decide) (f ((X ^ k) ^ 3)) := by
  apply Units.ext
  change f.mapMatrix (suslinCongDecide_kmMat q k) = 1 + Matrix.single 0 1 (f ((X ^ k) ^ 3))
  refine Matrix.ext fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp [RingHom.mapMatrix_apply, suslinCongDecide_kmMat, hq]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongDecide_map_km_of_C

/-- At `X = 0` (`k ≠ 0`): `h_{q,k} ↦ E₂₁(q³)`. -/
theorem suslinCongDecide_map_km_of_X {A S : Type*} [CommRing A] [CommRing S] (f : A[X] →+* S)
    (hX : f X = 0) (q : A) {k : ℕ} (hk : k ≠ 0) :
    elementaryMatrixUnitMap (ι := Fin 2) f (suslinCongDecide_km q k) =
      elementaryUnit (1 : Fin 2) 0 (by decide) (f (C q ^ 3)) := by
  apply Units.ext
  change f.mapMatrix (suslinCongDecide_kmMat q k) = 1 + Matrix.single 1 0 (f (C q ^ 3))
  refine Matrix.ext fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp [RingHom.mapMatrix_apply, suslinCongDecide_kmMat, hX, zero_pow hk]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongDecide_map_km_of_X

/-- **The witness** `σ_{q,k} = h_{q,k} · E₁₂(-X^{3k}) · E₂₁(-q³)`. -/
noncomputable def suslinCongDecide_wit {A : Type*} [CommRing A] (q : A) (k : ℕ) :
    (Matrix (Fin 2) (Fin 2) A[X])ˣ :=
  suslinCongDecide_km q k * elementaryUnit (0 : Fin 2) 1 (by decide) (-((X ^ k) ^ 3)) *
    elementaryUnit (1 : Fin 2) 0 (by decide) (-(C q ^ 3))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongDecide_wit

/-- `det σ_{q,k} = 1`. -/
theorem suslinCongDecide_wit_det {A : Type*} [CommRing A] (q : A) (k : ℕ) :
    Matrix.det (suslinCongDecide_wit q k : Matrix (Fin 2) (Fin 2) A[X]) = 1 := by
  have h1 := suslin_det_eq_one_of_mem_elementaryGroup
    (elementaryUnit_mem (0 : Fin 2) 1 (by decide) (-((X ^ k) ^ 3) : A[X]))
  have h2 := suslin_det_eq_one_of_mem_elementaryGroup
    (elementaryUnit_mem (1 : Fin 2) 0 (by decide) (-(C q ^ 3) : A[X]))
  rw [suslinCongDecide_wit, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, h1,
    h2, suslinCongDecide_km_det, mul_one, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongDecide_wit_det

/-- `σ_{q,k} ↦ 1` along every `f` killing `X` (`k ≠ 0`). -/
theorem suslinCongDecide_map_wit_of_X {A S : Type*} [CommRing A] [CommRing S]
    (f : A[X] →+* S) (hX : f X = 0) (q : A) {k : ℕ} (hk : k ≠ 0) :
    elementaryMatrixUnitMap (ι := Fin 2) f (suslinCongDecide_wit q k) = 1 := by
  have h0 : f (-((X ^ k) ^ 3)) = 0 := by
    rw [map_neg, map_pow, map_pow, hX, zero_pow hk, zero_pow three_ne_zero, neg_zero]
  have h1 : f (C q ^ 3) + f (-(C q ^ 3)) = 0 := by rw [map_neg, add_neg_cancel]
  rw [suslinCongDecide_wit, map_mul, map_mul, suslinCongDecide_map_km_of_X f hX q hk,
    elementaryMatrixUnitMap_elementaryUnit, elementaryMatrixUnitMap_elementaryUnit, h0,
    elementaryUnit_zero, mul_one, elementaryUnit_mul, h1, elementaryUnit_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongDecide_map_wit_of_X

/-- `σ_{q,k} ↦ 1` along every `f` killing `C q`. -/
theorem suslinCongDecide_map_wit_of_C {A S : Type*} [CommRing A] [CommRing S]
    (f : A[X] →+* S) {q : A} (hq : f (C q) = 0) (k : ℕ) :
    elementaryMatrixUnitMap (ι := Fin 2) f (suslinCongDecide_wit q k) = 1 := by
  have h0 : f (-(C q ^ 3)) = 0 := by
    rw [map_neg, map_pow, hq, zero_pow three_ne_zero, neg_zero]
  have h1 : f ((X ^ k) ^ 3) + f (-((X ^ k) ^ 3)) = 0 := by rw [map_neg, add_neg_cancel]
  rw [suslinCongDecide_wit, map_mul, map_mul, suslinCongDecide_map_km_of_C f hq k,
    elementaryMatrixUnitMap_elementaryUnit, elementaryMatrixUnitMap_elementaryUnit,
    elementaryUnit_mul, h1, elementaryUnit_zero, one_mul, h0, elementaryUnit_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongDecide_map_wit_of_C

/-- `σ_{q,k}(0) = 1` (`k ≠ 0`). -/
theorem suslinCongDecide_wit_const {A : Type*} [CommRing A] (q : A) {k : ℕ} (hk : k ≠ 0) :
    elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.constantCoeff (R := A))
      (suslinCongDecide_wit q k) = 1 :=
  suslinCongDecide_map_wit_of_X _ (by rw [Polynomial.constantCoeff_apply, coeff_X_zero]) q hk

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongDecide_wit_const

/-- `σ_{q,k} ≡ 1 mod I` whenever `q ∈ I`. -/
theorem suslinCongDecide_wit_mod {A : Type*} [CommRing A] {I : Ideal A} {q : A} (hq : q ∈ I)
    (k : ℕ) :
    elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.mapRingHom (Ideal.Quotient.mk I))
      (suslinCongDecide_wit q k) = 1 :=
  suslinCongDecide_map_wit_of_C _ (by
    rw [Polynomial.coe_mapRingHom, Polynomial.map_C, Ideal.Quotient.eq_zero_iff_mem.mpr hq,
      map_zero]) k

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongDecide_wit_mod

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
