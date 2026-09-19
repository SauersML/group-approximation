import GroupApproximation.Analysis.PrintedCornerCompression
import GroupApproximation.Meta.AxiomGuard

/-!
# The finite-dimensional projection corner as a full matrix algebra

This file contains the generic matrix-algebra identification behind corner
compression.  A matrix on the spectral range coordinates of a Hermitian
projection is extended by zero and conjugated out of the projection's
eigenbasis.  The resulting map is multiplicative, star preserving, and
isometric, and it sends the compressed matrix back to the corresponding
two-sided projection sandwich.
-/

namespace GroupApproximation

open Matrix
open KazhdanCornerMatrices
open PrintedCornerCompression
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## Zero extension of a principal block -/

/-- The zero extension of a matrix on a coordinate family to the ambient
coordinates.  This is the inverse of `principalBlock` on the corner. -/
def blockExtend {Y : Type*} (p : Y → Prop) [DecidablePred p]
    (C : Matrix {i : Y // p i} {i : Y // p i} ℂ) : Matrix Y Y ℂ :=
  Matrix.of fun i j ↦
    if hi : p i then (if hj : p j then C ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0

theorem blockExtend_apply {Y : Type*} (p : Y → Prop) [DecidablePred p]
    (C : Matrix {i : Y // p i} {i : Y // p i} ℂ) (i j : Y) :
    blockExtend p C i j =
      if hi : p i then (if hj : p j then C ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0 :=
  rfl

theorem blockExtend_apply_of_mem {Y : Type*} (p : Y → Prop) [DecidablePred p]
    (C : Matrix {i : Y // p i} {i : Y // p i} ℂ) (i j : Y) (hi : p i)
    (hj : p j) : blockExtend p C i j = C ⟨i, hi⟩ ⟨j, hj⟩ := by
  rw [blockExtend_apply, dif_pos hi, dif_pos hj]

theorem blockExtend_apply_of_not_left {Y : Type*} (p : Y → Prop)
    [DecidablePred p] (C : Matrix {i : Y // p i} {i : Y // p i} ℂ) (i j : Y)
    (hi : ¬ p i) : blockExtend p C i j = 0 := by
  rw [blockExtend_apply, dif_neg hi]

theorem blockExtend_apply_of_not_right {Y : Type*} (p : Y → Prop)
    [DecidablePred p] (C : Matrix {i : Y // p i} {i : Y // p i} ℂ) (i j : Y)
    (hj : ¬ p j) : blockExtend p C i j = 0 := by
  rw [blockExtend_apply]
  by_cases hi : p i
  · rw [dif_pos hi, dif_neg hj]
  · rw [dif_neg hi]

theorem blockExtend_sub {Y : Type*} (p : Y → Prop) [DecidablePred p]
    (C C' : Matrix {i : Y // p i} {i : Y // p i} ℂ) :
    blockExtend p (C - C') = blockExtend p C - blockExtend p C' := by
  ext i j
  rw [Matrix.sub_apply]
  by_cases hi : p i
  · by_cases hj : p j
    · rw [blockExtend_apply_of_mem p (C - C') i j hi hj,
        blockExtend_apply_of_mem p C i j hi hj,
        blockExtend_apply_of_mem p C' i j hi hj, Matrix.sub_apply]
    · rw [blockExtend_apply_of_not_right p (C - C') i j hj,
        blockExtend_apply_of_not_right p C i j hj,
        blockExtend_apply_of_not_right p C' i j hj, sub_zero]
  · rw [blockExtend_apply_of_not_left p (C - C') i j hi,
      blockExtend_apply_of_not_left p C i j hi,
      blockExtend_apply_of_not_left p C' i j hi, sub_zero]

theorem blockExtend_conjTranspose {Y : Type*} (p : Y → Prop)
    [DecidablePred p] (C : Matrix {i : Y // p i} {i : Y // p i} ℂ) :
    (blockExtend p C)ᴴ = blockExtend p Cᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hj : p j
  · by_cases hi : p i
    · rw [blockExtend_apply_of_mem p C j i hj hi,
        blockExtend_apply_of_mem p Cᴴ i j hi hj, Matrix.conjTranspose_apply]
    · rw [blockExtend_apply_of_not_right p C j i hi,
        blockExtend_apply_of_not_left p Cᴴ i j hi, star_zero]
  · rw [blockExtend_apply_of_not_left p C j i hj,
      blockExtend_apply_of_not_right p Cᴴ i j hj, star_zero]

theorem blockExtend_mul {Y : Type*} [Fintype Y] (p : Y → Prop)
    [DecidablePred p] (C C' : Matrix {i : Y // p i} {i : Y // p i} ℂ) :
    blockExtend p (C * C') = blockExtend p C * blockExtend p C' := by
  ext i j
  by_cases hi : p i
  · by_cases hj : p j
    · rw [blockExtend_apply_of_mem p (C * C') i j hi hj, Matrix.mul_apply,
        Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype p
          (fun k ↦ blockExtend p C i k * blockExtend p C' k j)]
      have h1 : (∑ k : {k : Y // p k},
            blockExtend p C i (k : Y) * blockExtend p C' (k : Y) j)
          = ∑ k : {k : Y // p k}, C ⟨i, hi⟩ k * C' k ⟨j, hj⟩ :=
        Finset.sum_congr rfl fun k _ ↦ by
          rw [blockExtend_apply_of_mem p C i (k : Y) hi k.2,
            blockExtend_apply_of_mem p C' (k : Y) j k.2 hj]
      have h2 : (∑ k : {k : Y // ¬ p k},
            blockExtend p C i (k : Y) * blockExtend p C' (k : Y) j) = 0 :=
        Finset.sum_eq_zero fun k _ ↦ by
          rw [blockExtend_apply_of_not_left p C' (k : Y) j k.2, mul_zero]
      rw [h1, h2, add_zero]
    · rw [blockExtend_apply_of_not_right p (C * C') i j hj, Matrix.mul_apply]
      exact (Finset.sum_eq_zero fun k _ ↦ by
        rw [blockExtend_apply_of_not_right p C' k j hj, mul_zero]).symm
  · rw [blockExtend_apply_of_not_left p (C * C') i j hi, Matrix.mul_apply]
    exact (Finset.sum_eq_zero fun k _ ↦ by
      rw [blockExtend_apply_of_not_left p C i k hi, zero_mul]).symm

theorem principalBlock_blockExtend {Y : Type*} (p : Y → Prop)
    [DecidablePred p] (C : Matrix {i : Y // p i} {i : Y // p i} ℂ) :
    principalBlock p (blockExtend p C) = C := by
  ext i j
  exact blockExtend_apply_of_mem p C (i : Y) (j : Y) i.2 j.2

/-- The zero extension of a principal block is the two-sided coordinate cut. -/
theorem blockExtend_principalBlock {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p : Y → Prop) [DecidablePred p] (M : Matrix Y Y ℂ) :
    blockExtend p (principalBlock p M)
      = coordinateProjection p * M * coordinateProjection p := by
  have hentry : ∀ a b : Y,
      (coordinateProjection p * M * coordinateProjection p) a b
        = (if p a then (1 : ℂ) else 0) * M a b *
          (if p b then (1 : ℂ) else 0) := by
    intro a b
    rw [coordinateProjection, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ext i j
  rw [hentry i j, blockExtend_apply]
  by_cases hi : p i
  · by_cases hj : p j
    · rw [dif_pos hi, dif_pos hj, if_pos hi, if_pos hj, one_mul, mul_one]
      rfl
    · rw [dif_pos hi, dif_neg hj, if_neg hj, mul_zero]
  · rw [dif_neg hi, if_neg hi, zero_mul, zero_mul]

theorem blockExtend_mulVec_apply {Y : Type*} [Fintype Y] (p : Y → Prop)
    [DecidablePred p] (C : Matrix {i : Y // p i} {i : Y // p i} ℂ)
    (x : Y → ℂ) {i : Y} (hi : p i) :
    (blockExtend p C *ᵥ x) i
      = (C *ᵥ fun j : {j : Y // p j} ↦ x (j : Y)) ⟨i, hi⟩ := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Fintype.sum_subtype_add_sum_subtype p
    (fun j ↦ blockExtend p C i j * x j)]
  have h1 : (∑ j : {j : Y // p j}, blockExtend p C i (j : Y) * x (j : Y))
      = ∑ j : {j : Y // p j}, C ⟨i, hi⟩ j * x (j : Y) :=
    Finset.sum_congr rfl fun j _ ↦ by
      rw [blockExtend_apply_of_mem p C i (j : Y) hi j.2]
  have h2 : (∑ j : {j : Y // ¬ p j},
      blockExtend p C i (j : Y) * x (j : Y)) = 0 :=
    Finset.sum_eq_zero fun j _ ↦ by
      rw [blockExtend_apply_of_not_right p C i (j : Y) j.2, zero_mul]
  rw [h1, h2, add_zero]

theorem blockExtend_mulVec_eq_zero {Y : Type*} [Fintype Y] (p : Y → Prop)
    [DecidablePred p] (C : Matrix {i : Y // p i} {i : Y // p i} ℂ)
    (x : Y → ℂ) {i : Y} (hi : ¬ p i) : (blockExtend p C *ᵥ x) i = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_eq_zero fun j _ ↦ by
    rw [blockExtend_apply_of_not_left p C i j hi, zero_mul]

/-- Zero extension is contractive. -/
theorem norm_blockExtend_le {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p : Y → Prop) [DecidablePred p]
    (C : Matrix {i : Y // p i} {i : Y // p i} ℂ) :
    ‖blockExtend p C‖ ≤ ‖C‖ := by
  refine l2_opNorm_le_of_sum_normSq_general (blockExtend p C) (norm_nonneg C)
    fun x ↦ ?_
  have hrestrict : ∀ i : {i : Y // p i},
      (blockExtend p C *ᵥ x) (i : Y)
        = (C *ᵥ fun j : {j : Y // p j} ↦ x (j : Y)) i :=
    fun i ↦ blockExtend_mulVec_apply p C x i.2
  have hzero : ∀ i : {i : Y // ¬ p i}, (blockExtend p C *ᵥ x) (i : Y) = 0 :=
    fun i ↦ blockExtend_mulVec_eq_zero p C x i.2
  have hle : (∑ i : {i : Y // p i},
        Complex.normSq ((fun j : {j : Y // p j} ↦ x (j : Y)) i))
      ≤ ∑ i : Y, Complex.normSq (x i) := by
    rw [← Fintype.sum_subtype_add_sum_subtype p
      (fun i ↦ Complex.normSq (x i))]
    exact le_add_of_nonneg_right
      (Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _)
  rw [← Fintype.sum_subtype_add_sum_subtype p
    (fun i ↦ Complex.normSq ((blockExtend p C *ᵥ x) i))]
  simp only [hrestrict, hzero, Complex.normSq_zero, Finset.sum_const_zero,
    add_zero]
  refine (sum_normSq_mulVec_le_general C
    (fun j : {j : Y // p j} ↦ x (j : Y))).trans ?_
  exact mul_le_mul_of_nonneg_left hle (sq_nonneg ‖C‖)

/-- Zero extension is isometric. -/
theorem norm_blockExtend {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p : Y → Prop) [DecidablePred p]
    (C : Matrix {i : Y // p i} {i : Y // p i} ℂ) :
    ‖blockExtend p C‖ = ‖C‖ := by
  refine le_antisymm (norm_blockExtend_le p C) ?_
  have h := norm_principalBlock_le p (blockExtend p C)
  rwa [principalBlock_blockExtend] at h

/-! ## The projection corner in ambient coordinates -/

/-- A matrix on the range coordinates of `q`, extended by zero and conjugated
back out of the eigenbasis of `q`. -/
def cornerEmbed {Y : Type*} [Fintype Y] [DecidableEq Y] {q : Matrix Y Y ℂ}
    (hq : q.IsHermitian)
    (C : Matrix {i : Y // cornerPredicate hq i} {i : Y // cornerPredicate hq i} ℂ) :
    Matrix Y Y ℂ :=
  eigenUnitary hq * blockExtend (cornerPredicate hq) C * (eigenUnitary hq)ᴴ

theorem cornerEmbed_sub {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    (C C' : Matrix {i : Y // cornerPredicate hq i}
      {i : Y // cornerPredicate hq i} ℂ) :
    cornerEmbed hq (C - C') = cornerEmbed hq C - cornerEmbed hq C' := by
  simp only [cornerEmbed, blockExtend_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem cornerEmbed_conjTranspose {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    (C : Matrix {i : Y // cornerPredicate hq i}
      {i : Y // cornerPredicate hq i} ℂ) :
    (cornerEmbed hq C)ᴴ = cornerEmbed hq Cᴴ := by
  simp only [cornerEmbed, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, blockExtend_conjTranspose,
    Matrix.mul_assoc]

theorem cornerEmbed_mul {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    (C C' : Matrix {i : Y // cornerPredicate hq i}
      {i : Y // cornerPredicate hq i} ℂ) :
    cornerEmbed hq (C * C') = cornerEmbed hq C * cornerEmbed hq C' := by
  simp only [cornerEmbed, blockExtend_mul]
  rw [show (eigenUnitary hq * blockExtend (cornerPredicate hq) C *
        (eigenUnitary hq)ᴴ) *
        (eigenUnitary hq * blockExtend (cornerPredicate hq) C' *
          (eigenUnitary hq)ᴴ)
      = eigenUnitary hq * blockExtend (cornerPredicate hq) C *
          ((eigenUnitary hq)ᴴ * eigenUnitary hq) *
          blockExtend (cornerPredicate hq) C' * (eigenUnitary hq)ᴴ by
      noncomm_ring, eigenUnitary_conjTranspose_mul]
  noncomm_ring

theorem norm_cornerEmbed {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    (C : Matrix {i : Y // cornerPredicate hq i}
      {i : Y // cornerPredicate hq i} ℂ) :
    ‖cornerEmbed hq C‖ = ‖C‖ := by
  rw [cornerEmbed, norm_unitary_conj (eigenUnitary_mem hq), norm_blockExtend]

/-- Embedding a compressed matrix recovers its projection sandwich. -/
theorem cornerEmbed_cornerCompression {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q : Matrix Y Y ℂ} (hq : q.IsHermitian) (hidem : q * q = q)
    (A : Matrix Y Y ℂ) :
    cornerEmbed hq (cornerCompression hq A) = q * A * q := by
  have hblock : blockExtend (cornerPredicate hq) (cornerCompression hq A)
      = eigenbasisConj hq q * eigenbasisConj hq A * eigenbasisConj hq q := by
    rw [cornerCompression, blockExtend_principalBlock,
      ← eigenbasisConj_eq_coordinateProjection hq hidem]
  have hconj : eigenbasisConj hq q * eigenbasisConj hq A * eigenbasisConj hq q
      = eigenbasisConj hq (q * A * q) := by
    simp only [eigenbasisConj]
    rw [show ((eigenUnitary hq)ᴴ * q * eigenUnitary hq) *
          ((eigenUnitary hq)ᴴ * A * eigenUnitary hq) *
          ((eigenUnitary hq)ᴴ * q * eigenUnitary hq)
        = (eigenUnitary hq)ᴴ * q * (eigenUnitary hq * (eigenUnitary hq)ᴴ) *
            A * (eigenUnitary hq * (eigenUnitary hq)ᴴ) * q *
            eigenUnitary hq by noncomm_ring, eigenUnitary_mul_conjTranspose]
    noncomm_ring
  have hcancel : eigenUnitary hq * eigenbasisConj hq (q * A * q) *
      (eigenUnitary hq)ᴴ = q * A * q := by
    simp only [eigenbasisConj]
    rw [show eigenUnitary hq *
          ((eigenUnitary hq)ᴴ * (q * A * q) * eigenUnitary hq) *
          (eigenUnitary hq)ᴴ
        = (eigenUnitary hq * (eigenUnitary hq)ᴴ) * (q * A * q) *
            (eigenUnitary hq * (eigenUnitary hq)ᴴ) by noncomm_ring,
      eigenUnitary_mul_conjTranspose]
    noncomm_ring
  rw [cornerEmbed, hblock, hconj, hcancel]

#audit_axioms norm_blockExtend
#audit_axioms norm_cornerEmbed
#audit_axioms cornerEmbed_cornerCompression

end

end GroupApproximation
