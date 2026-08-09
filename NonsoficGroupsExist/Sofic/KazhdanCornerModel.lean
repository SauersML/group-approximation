import NonsoficGroupsExist.Sofic.KazhdanCornerCompression
import NonsoficGroupsExist.Sofic.HyperlinearUltraproductBridge

/-!
# Finite moving-corner models

This file realizes the complementary spectral cutoff as an honest smaller
matrix algebra.  The coordinates are the eigenvectors whose Hermitian-average
eigenvalue is at most the cutoff.  Principal compression is contractive in
the matrix `ℓ²` operator norm, and the almost-reducing estimates from
`KazhdanCornerCompression` therefore pass to these smaller matrices.
-/

namespace NonsoficGroupsExist
namespace KazhdanCornerMatrices

open Matrix
open scoped Matrix.Norms.L2Operator

/-! ## Principal compression -/

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The moving spectral coordinates below a threshold. -/
def MovingIndex (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (t : ℝ) :=
  {i : Y // hH.eigenvalues i ≤ t}

noncomputable instance (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (t : ℝ) :
    Fintype (MovingIndex H hH t) := by
  letI : Finite (MovingIndex H hH t) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (t : ℝ) :
    DecidableEq (MovingIndex H hH t) := Classical.decEq _

/-- Principal matrix block on a decidable family of coordinates. -/
def principalBlock (p : Y → Prop) [DecidablePred p] (C : Matrix Y Y ℂ) :
    Matrix {i // p i} {i // p i} ℂ := C.toBlock p p

/-- A zero extension from a coordinate family to the ambient coordinates. -/
def extendByZero (p : Y → Prop) [DecidablePred p]
    (x : {i // p i} → ℂ) : Y → ℂ :=
  fun i ↦ if hi : p i then x ⟨i, hi⟩ else 0

omit [Fintype Y] [DecidableEq Y] in
theorem extendByZero_apply (p : Y → Prop) [DecidablePred p]
    (x : {i // p i} → ℂ) (i : {i // p i}) :
    extendByZero p x i = x i := by
  simp [extendByZero, i.2]

omit [DecidableEq Y] in
/-- A principal block acts as the restriction of the ambient matrix acting
on the zero extension. -/
theorem principalBlock_mulVec (p : Y → Prop) [DecidablePred p]
    (C : Matrix Y Y ℂ) (x : {i // p i} → ℂ) (i : {i // p i}) :
    (principalBlock p C *ᵥ x) i = (C *ᵥ extendByZero p x) i := by
  classical
  simp only [principalBlock, Matrix.toBlock_apply, Matrix.mulVec, dotProduct]
  rw [← Fintype.sum_subtype_add_sum_subtype p
    (fun j ↦ C i j * extendByZero p x j)]
  have hpos : (∑ j : {j // p j}, C i j * extendByZero p x j) =
      ∑ j : {j // p j}, C i j * x j := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [extendByZero, j.2]
  have hneg : (∑ j : {j // ¬p j}, C i j * extendByZero p x j) = 0 := by
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    simp [extendByZero, j.2]
  rw [hpos, hneg, add_zero]

/-- Squared Euclidean norm, in entrywise form, for an arbitrary finite
coordinate type. -/
theorem euclidean_norm_sq_general {Z : Type*} [Fintype Z]
    (w : Z → ℂ) :
    ‖(EuclideanSpace.equiv Z ℂ).symm w‖ ^ 2 =
      ∑ i : Z, Complex.normSq (w i) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun i _ ↦ (Complex.normSq_eq_norm_sq _).symm

/-- General finite-type version of the operator-norm vector criterion. -/
theorem l2_opNorm_le_of_sum_normSq_general {Z : Type*} [Fintype Z]
    [DecidableEq Z] (C : Matrix Z Z ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x : Z → ℂ, ∑ i : Z, Complex.normSq ((C *ᵥ x) i) ≤
      M ^ 2 * ∑ i : Z, Complex.normSq (x i)) :
    ‖C‖ ≤ M := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x ↦ ?_
  have hL : ‖(EuclideanSpace.equiv Z ℂ).symm (C *ᵥ x)‖ ^ 2 =
      ∑ i : Z, Complex.normSq ((C *ᵥ x) i) :=
    euclidean_norm_sq_general _
  have hR : ‖(EuclideanSpace.equiv Z ℂ).symm x‖ ^ 2 =
      ∑ i : Z, Complex.normSq (x i) := euclidean_norm_sq_general _
  have hval : ‖(LinearEquiv.trans
      (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Z) (n := Z))
      LinearMap.toContinuousLinearMap C) x‖ =
      ‖(EuclideanSpace.equiv Z ℂ).symm (C *ᵥ x)‖ := rfl
  rw [hval]
  have hsquares : ‖(EuclideanSpace.equiv Z ℂ).symm (C *ᵥ x)‖ ^ 2 ≤
      (M * ‖x‖) ^ 2 := by
    rw [hL, mul_pow]
    have hxx : ‖x‖ ^ 2 = ∑ i : Z, Complex.normSq (x i) := hR
    rw [hxx]
    exact h x
  have hleft : 0 ≤ ‖(EuclideanSpace.equiv Z ℂ).symm (C *ᵥ x)‖ :=
    norm_nonneg _
  have hright : 0 ≤ M * ‖x‖ := mul_nonneg hM (norm_nonneg _)
  nlinarith

/-- The operator norm bounds every matrix-vector product, for an arbitrary
finite coordinate type. -/
theorem sum_normSq_mulVec_le_general {Z : Type*} [Fintype Z]
    [DecidableEq Z] (C : Matrix Z Z ℂ) (x : Z → ℂ) :
    ∑ i : Z, Complex.normSq ((C *ᵥ x) i) ≤
      ‖C‖ ^ 2 * ∑ i : Z, Complex.normSq (x i) := by
  have h : ‖(EuclideanSpace.equiv Z ℂ).symm (C *ᵥ x)‖ ≤
      ‖C‖ * ‖(EuclideanSpace.equiv Z ℂ).symm x‖ :=
    Matrix.l2_opNorm_mulVec C ((EuclideanSpace.equiv Z ℂ).symm x)
  have hL := euclidean_norm_sq_general (C *ᵥ x)
  have hR := euclidean_norm_sq_general x
  have hsquare : ‖(EuclideanSpace.equiv Z ℂ).symm (C *ᵥ x)‖ ^ 2 ≤
      (‖C‖ * ‖(EuclideanSpace.equiv Z ℂ).symm x‖) ^ 2 := by
    nlinarith [norm_nonneg ((EuclideanSpace.equiv Z ℂ).symm (C *ᵥ x)),
      norm_nonneg C, norm_nonneg ((EuclideanSpace.equiv Z ℂ).symm x)]
  calc
    ∑ i : Z, Complex.normSq ((C *ᵥ x) i) =
        ‖(EuclideanSpace.equiv Z ℂ).symm (C *ᵥ x)‖ ^ 2 := hL.symm
    _ ≤ (‖C‖ * ‖(EuclideanSpace.equiv Z ℂ).symm x‖) ^ 2 := hsquare
    _ = ‖C‖ ^ 2 * ∑ i : Z, Complex.normSq (x i) := by
      rw [mul_pow, hR]

/-- Principal compression cannot increase the matrix operator norm. -/
theorem norm_principalBlock_le (p : Y → Prop) [DecidablePred p]
    (C : Matrix Y Y ℂ) : ‖principalBlock p C‖ ≤ ‖C‖ := by
  classical
  refine l2_opNorm_le_of_sum_normSq_general (principalBlock p C)
    (norm_nonneg C) fun x ↦ ?_
  let xhat := extendByZero p x
  have hout :
      ∑ i : {i // p i}, Complex.normSq ((principalBlock p C *ᵥ x) i) ≤
        ∑ i : Y, Complex.normSq ((C *ᵥ xhat) i) := by
    rw [← Fintype.sum_subtype_add_sum_subtype p
      (fun i ↦ Complex.normSq ((C *ᵥ xhat) i))]
    simp only [principalBlock_mulVec]
    exact le_add_of_nonneg_right
      (Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _)
  have hin : ∑ i : Y, Complex.normSq (xhat i) =
      ∑ i : {i // p i}, Complex.normSq (x i) := by
    rw [← Fintype.sum_subtype_add_sum_subtype p
      (fun i ↦ Complex.normSq (xhat i))]
    have hpos : (∑ i : {i // p i}, Complex.normSq (xhat i)) =
        ∑ i : {i // p i}, Complex.normSq (x i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp [xhat, extendByZero, i.2]
    have hneg : (∑ i : {i // ¬p i}, Complex.normSq (xhat i)) = 0 := by
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      simp [xhat, extendByZero, i.2]
    rw [hpos, hneg, add_zero]
  calc
    ∑ i : {i // p i}, Complex.normSq ((principalBlock p C *ᵥ x) i)
        ≤ ∑ i : Y, Complex.normSq ((C *ᵥ xhat) i) := hout
    _ ≤ ‖C‖ ^ 2 * ∑ i : Y, Complex.normSq (xhat i) := by
      exact sum_normSq_mulVec_le_general C xhat
    _ = ‖C‖ ^ 2 * ∑ i : {i // p i}, Complex.normSq (x i) := by
      rw [hin]

end KazhdanCornerMatrices
end NonsoficGroupsExist
