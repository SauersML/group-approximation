import GroupApproximation.Sofic.KazhdanCornerCompression
import GroupApproximation.Sofic.HyperlinearUltraproductBridge

/-!
# Finite moving-corner models

This file realizes the complementary spectral cutoff as an honest smaller
matrix algebra.  The coordinates are the eigenvectors whose Hermitian-average
eigenvalue is at most the cutoff.  Principal compression is contractive in
the matrix `ℓ²` operator norm, and the almost-reducing estimates from
`KazhdanCornerCompression` therefore pass to these smaller matrices.
-/

namespace GroupApproximation
namespace KazhdanCornerMatrices

open Matrix
open scoped Matrix.Norms.L2Operator

/-! ## Principal compression -/

variable {Y : Type*}

/-- Principal matrix block on a decidable family of coordinates. -/
def coordinateBlock (p q : Y → Prop)
    (C : Matrix Y Y ℂ) : Matrix {i // p i} {i // q i} ℂ :=
  C.toBlock p q

/-- Principal matrix block on a decidable family of coordinates. -/
def principalBlock (p : Y → Prop) (C : Matrix Y Y ℂ) :
    Matrix {i // p i} {i // p i} ℂ := coordinateBlock p p C

/-- A zero extension from a coordinate family to the ambient coordinates. -/
def extendByZero (p : Y → Prop) [DecidablePred p]
    (x : {i // p i} → ℂ) : Y → ℂ :=
  fun i ↦ if hi : p i then x ⟨i, hi⟩ else 0

/-- A principal block acts as the restriction of the ambient matrix acting
on the zero extension. -/
theorem principalBlock_mulVec [Fintype Y] (p : Y → Prop) [DecidablePred p]
    (C : Matrix Y Y ℂ) (x : {i // p i} → ℂ) (i : {i // p i}) :
    (principalBlock p C *ᵥ x) i = (C *ᵥ extendByZero p x) i := by
  classical
  simp only [principalBlock, coordinateBlock, Matrix.toBlock_apply,
    Matrix.mulVec, dotProduct]
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
theorem l2_opNorm_le_of_sum_normSq_general
    {R Z : Type*} [Fintype R] [Fintype Z] [DecidableEq Z]
    (C : Matrix R Z ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x : Z → ℂ, ∑ i : R, Complex.normSq ((C *ᵥ x) i) ≤
      M ^ 2 * ∑ i : Z, Complex.normSq (x i)) :
    ‖C‖ ≤ M := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x ↦ ?_
  have hL : ‖(EuclideanSpace.equiv R ℂ).symm (C *ᵥ x)‖ ^ 2 =
      ∑ i : R, Complex.normSq ((C *ᵥ x) i) :=
    euclidean_norm_sq_general _
  have hR : ‖(EuclideanSpace.equiv Z ℂ).symm x‖ ^ 2 =
      ∑ i : Z, Complex.normSq (x i) := euclidean_norm_sq_general _
  have hval : ‖(LinearEquiv.trans
      (Matrix.toEuclideanLin (𝕜 := ℂ) (m := R) (n := Z))
      LinearMap.toContinuousLinearMap C) x‖ =
      ‖(EuclideanSpace.equiv R ℂ).symm (C *ᵥ x)‖ := rfl
  rw [hval]
  have hsquares : ‖(EuclideanSpace.equiv R ℂ).symm (C *ᵥ x)‖ ^ 2 ≤
      (M * ‖x‖) ^ 2 := by
    rw [hL, mul_pow]
    have hxx : ‖x‖ ^ 2 = ∑ i : Z, Complex.normSq (x i) := hR
    rw [hxx]
    exact h x
  have hleft : 0 ≤ ‖(EuclideanSpace.equiv R ℂ).symm (C *ᵥ x)‖ :=
    norm_nonneg _
  have hright : 0 ≤ M * ‖x‖ := mul_nonneg hM (norm_nonneg _)
  nlinarith only [hsquares, hleft, hright]

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
    nlinarith only [h, norm_nonneg ((EuclideanSpace.equiv Z ℂ).symm (C *ᵥ x)),
      norm_nonneg C, norm_nonneg ((EuclideanSpace.equiv Z ℂ).symm x)]
  calc
    ∑ i : Z, Complex.normSq ((C *ᵥ x) i) =
        ‖(EuclideanSpace.equiv Z ℂ).symm (C *ᵥ x)‖ ^ 2 := hL.symm
    _ ≤ (‖C‖ * ‖(EuclideanSpace.equiv Z ℂ).symm x‖) ^ 2 := hsquare
    _ = ‖C‖ ^ 2 * ∑ i : Z, Complex.normSq (x i) := by
      rw [mul_pow, hR]

/-- Principal compression cannot increase the matrix operator norm. -/
theorem norm_principalBlock_le [Fintype Y] [DecidableEq Y]
    (p : Y → Prop) [DecidablePred p]
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
    _ ≤ ‖C‖ ^ 2 * ∑ i : Y, Complex.normSq (xhat i) :=
      sum_normSq_mulVec_le_general C xhat
    _ = ‖C‖ ^ 2 * ∑ i : {i // p i}, Complex.normSq (x i) := by
      rw [hin]

/-- A rectangular coordinate block acts as the corresponding restriction
after zero extension in the column coordinates. -/
theorem coordinateBlock_mulVec [Fintype Y] (p q : Y → Prop)
    [DecidablePred q] (C : Matrix Y Y ℂ)
    (x : {i // q i} → ℂ) (i : {i // p i}) :
    (coordinateBlock p q C *ᵥ x) i =
      (C *ᵥ extendByZero q x) i := by
  classical
  simp only [coordinateBlock, Matrix.toBlock_apply, Matrix.mulVec, dotProduct]
  rw [← Fintype.sum_subtype_add_sum_subtype q
    (fun j ↦ C i j * extendByZero q x j)]
  have hpos : (∑ j : {j // q j}, C i j * extendByZero q x j) =
      ∑ j : {j // q j}, C i j * x j := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [extendByZero, j.2]
  have hneg : (∑ j : {j // ¬q j}, C i j * extendByZero q x j) = 0 := by
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    simp [extendByZero, j.2]
  rw [hpos, hneg, add_zero]

/-- Every rectangular coordinate block is an operator-norm contraction of
the ambient matrix. -/
theorem norm_coordinateBlock_le [Fintype Y] [DecidableEq Y]
    (p q : Y → Prop)
    [DecidablePred p] [DecidablePred q] (C : Matrix Y Y ℂ) :
    ‖coordinateBlock p q C‖ ≤ ‖C‖ := by
  classical
  refine l2_opNorm_le_of_sum_normSq_general (coordinateBlock p q C)
    (norm_nonneg C) fun x ↦ ?_
  let xhat := extendByZero q x
  have hout :
      ∑ i : {i // p i}, Complex.normSq ((coordinateBlock p q C *ᵥ x) i) ≤
        ∑ i : Y, Complex.normSq ((C *ᵥ xhat) i) := by
    rw [← Fintype.sum_subtype_add_sum_subtype p
      (fun i ↦ Complex.normSq ((C *ᵥ xhat) i))]
    simp only [coordinateBlock_mulVec]
    exact le_add_of_nonneg_right
      (Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _)
  have hin : ∑ i : Y, Complex.normSq (xhat i) =
      ∑ i : {i // q i}, Complex.normSq (x i) := by
    rw [← Fintype.sum_subtype_add_sum_subtype q
      (fun i ↦ Complex.normSq (xhat i))]
    have hpos : (∑ i : {i // q i}, Complex.normSq (xhat i)) =
        ∑ i : {i // q i}, Complex.normSq (x i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp [xhat, extendByZero, i.2]
    have hneg : (∑ i : {i // ¬q i}, Complex.normSq (xhat i)) = 0 := by
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      simp [xhat, extendByZero, i.2]
    rw [hpos, hneg, add_zero]
  calc
    ∑ i : {i // p i}, Complex.normSq ((coordinateBlock p q C *ᵥ x) i)
        ≤ ∑ i : Y, Complex.normSq ((C *ᵥ xhat) i) := hout
    _ ≤ ‖C‖ ^ 2 * ∑ i : Y, Complex.normSq (xhat i) :=
      sum_normSq_mulVec_le_general C xhat
    _ = ‖C‖ ^ 2 * ∑ i : {i // q i}, Complex.normSq (x i) := by
      rw [hin]

@[simp] theorem principalBlock_conjTranspose (p : Y → Prop)
    (C : Matrix Y Y ℂ) :
    (principalBlock p C)ᴴ = principalBlock p Cᴴ := by
  ext i j
  rfl

@[simp] theorem coordinateBlock_conjTranspose (p q : Y → Prop)
    (C : Matrix Y Y ℂ) :
    (coordinateBlock p q C)ᴴ = coordinateBlock q p Cᴴ := by
  ext i j
  rfl

@[simp] theorem principalBlock_sub (p : Y → Prop)
    (C D : Matrix Y Y ℂ) :
    principalBlock p (C - D) = principalBlock p C - principalBlock p D := by
  rfl

@[simp] theorem principalBlock_one [DecidableEq Y]
    (p : Y → Prop) :
    principalBlock p (1 : Matrix Y Y ℂ) = 1 := by
  ext i j
  simp [principalBlock, coordinateBlock, Matrix.toBlock_apply,
    Matrix.one_apply, Subtype.ext_iff]

/-- Multiplication splits into the retained intermediate coordinates and the
off-diagonal cross term. -/
theorem principalBlock_mul_eq_add_cross [Fintype Y]
    (p : Y → Prop) [DecidablePred p]
    (C D : Matrix Y Y ℂ) :
    principalBlock p (C * D) =
      principalBlock p C * principalBlock p D +
        coordinateBlock p (fun i ↦ ¬p i) C *
          coordinateBlock (fun i ↦ ¬p i) p D := by
  simpa only [principalBlock, coordinateBlock] using
    Matrix.toBlock_mul_eq_add p p p C D

variable [Fintype Y] [DecidableEq Y]

/-- Generic principal-compression multiplicativity estimate. -/
theorem norm_principalBlock_mul_defect_le (p : Y → Prop) [DecidablePred p]
    (A B C : Matrix Y Y ℂ) :
    ‖principalBlock p A - principalBlock p B * principalBlock p C‖ ≤
      ‖A - B * C‖ +
        ‖coordinateBlock p (fun i ↦ ¬p i) B‖ *
          ‖coordinateBlock (fun i ↦ ¬p i) p C‖ := by
  have hsplit : principalBlock p A - principalBlock p B * principalBlock p C =
      principalBlock p (A - B * C) +
        coordinateBlock p (fun i ↦ ¬p i) B *
          coordinateBlock (fun i ↦ ¬p i) p C := by
    rw [principalBlock_sub, principalBlock_mul_eq_add_cross]
    abel
  rw [hsplit]
  calc
    ‖principalBlock p (A - B * C) +
        coordinateBlock p (fun i ↦ ¬p i) B *
          coordinateBlock (fun i ↦ ¬p i) p C‖ ≤
      ‖principalBlock p (A - B * C)‖ +
        ‖coordinateBlock p (fun i ↦ ¬p i) B *
          coordinateBlock (fun i ↦ ¬p i) p C‖ := norm_add_le _ _
    _ ≤ ‖A - B * C‖ +
        ‖coordinateBlock p (fun i ↦ ¬p i) B‖ *
          ‖coordinateBlock (fun i ↦ ¬p i) p C‖ :=
      add_le_add (norm_principalBlock_le p _)
        (Matrix.l2_opNorm_mul _ _)

/-- Generic Gram-defect estimate for a principal compression of a unitary. -/
theorem norm_principalBlock_gram_sub_one_le (p : Y → Prop)
    [DecidablePred p] (V : Matrix Y Y ℂ) (hV : Vᴴ * V = 1) :
    ‖cornerGram (principalBlock p V) - 1‖ ≤
      ‖coordinateBlock (fun i ↦ ¬p i) p V‖ ^ 2 := by
  have hdecomp := principalBlock_mul_eq_add_cross p Vᴴ V
  rw [hV, principalBlock_one] at hdecomp
  have heq : cornerGram (principalBlock p V) - 1 =
      -(coordinateBlock p (fun i ↦ ¬p i) Vᴴ *
        coordinateBlock (fun i ↦ ¬p i) p V) := by
    simp only [cornerGram, principalBlock_conjTranspose]
    rw [hdecomp]
    abel
  rw [heq, norm_neg]
  calc
    ‖coordinateBlock p (fun i ↦ ¬p i) Vᴴ *
        coordinateBlock (fun i ↦ ¬p i) p V‖ ≤
      ‖coordinateBlock p (fun i ↦ ¬p i) Vᴴ‖ *
        ‖coordinateBlock (fun i ↦ ¬p i) p V‖ := Matrix.l2_opNorm_mul _ _
    _ = ‖coordinateBlock (fun i ↦ ¬p i) p V‖ ^ 2 := by
      rw [← coordinateBlock_conjTranspose,
        Matrix.l2_opNorm_conjTranspose, pow_two]

/-! ## Weak-MF moving coordinates -/

section WeakMF

variable {G : Type} [Group G]

/-- If every Hermitian eigenvalue lies above the threshold, the top spectral
cutoff is the identity. -/
theorem spectralAbove_eq_one_of_forall_lt (H : Matrix Y Y ℂ)
    (hH : H.IsHermitian) (t : ℝ) (h : ∀ i, t < hH.eigenvalues i) :
    spectralAbove H hH t = 1 := by
  unfold spectralAbove
  simp_rw [if_pos (h _)]
  rw [show Matrix.diagonal (fun _ : Y ↦ (1 : ℂ)) = 1 by ext i j; simp]
  rw [Matrix.mul_one]
  exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2

end WeakMF

end KazhdanCornerMatrices
end GroupApproximation
