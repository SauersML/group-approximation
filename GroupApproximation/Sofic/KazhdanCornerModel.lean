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
def coordinateBlock (p q : Y → Prop) [DecidablePred p] [DecidablePred q]
    (C : Matrix Y Y ℂ) : Matrix {i // p i} {i // q i} ℂ :=
  C.toBlock p q

/-- Principal matrix block on a decidable family of coordinates. -/
def principalBlock (p : Y → Prop) [DecidablePred p] (C : Matrix Y Y ℂ) :
    Matrix {i // p i} {i // p i} ℂ := coordinateBlock p p C

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

omit [DecidableEq Y] in
/-- A rectangular coordinate block acts as the corresponding restriction
after zero extension in the column coordinates. -/
theorem coordinateBlock_mulVec (p q : Y → Prop)
    [DecidablePred p] [DecidablePred q] (C : Matrix Y Y ℂ)
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
theorem norm_coordinateBlock_le (p q : Y → Prop)
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

omit [Fintype Y] [DecidableEq Y] in
@[simp] theorem principalBlock_conjTranspose (p : Y → Prop)
    [DecidablePred p] (C : Matrix Y Y ℂ) :
    (principalBlock p C)ᴴ = principalBlock p Cᴴ := by
  ext i j
  rfl

omit [Fintype Y] [DecidableEq Y] in
@[simp] theorem coordinateBlock_conjTranspose (p q : Y → Prop)
    [DecidablePred p] [DecidablePred q] (C : Matrix Y Y ℂ) :
    (coordinateBlock p q C)ᴴ = coordinateBlock q p Cᴴ := by
  ext i j
  rfl

omit [Fintype Y] [DecidableEq Y] in
@[simp] theorem principalBlock_sub (p : Y → Prop) [DecidablePred p]
    (C D : Matrix Y Y ℂ) :
    principalBlock p (C - D) = principalBlock p C - principalBlock p D := by
  rfl

omit [Fintype Y] in
@[simp] theorem principalBlock_one (p : Y → Prop) [DecidablePred p] :
    principalBlock p (1 : Matrix Y Y ℂ) = 1 := by
  ext i j
  simp [principalBlock, coordinateBlock, Matrix.toBlock_apply,
    Matrix.one_apply, Subtype.ext_iff]

omit [DecidableEq Y] in
/-- Multiplication splits into the retained intermediate coordinates and the
off-diagonal cross term. -/
theorem principalBlock_mul_eq_add_cross (p : Y → Prop) [DecidablePred p]
    (C D : Matrix Y Y ℂ) :
    principalBlock p (C * D) =
      principalBlock p C * principalBlock p D +
        coordinateBlock p (fun i ↦ ¬p i) C *
          coordinateBlock (fun i ↦ ¬p i) p D := by
  simpa only [principalBlock, coordinateBlock] using
    Matrix.toBlock_mul_eq_add p p p C D

/-- A block between disjoint coordinate families is bounded by the residual
on its column family. -/
theorem norm_coordinateBlock_disjoint_le_residual
    (p q : Y → Prop) [DecidablePred p] [DecidablePred q]
    (hdisj : ∀ i, p i → q i → False) (C : Matrix Y Y ℂ) :
    ‖coordinateBlock p q C‖ ≤
      ‖(C - 1) * Matrix.diagonal (fun i ↦ if q i then (1 : ℂ) else 0)‖ := by
  have heq : coordinateBlock p q C = coordinateBlock p q
      ((C - 1) * Matrix.diagonal (fun i ↦ if q i then (1 : ℂ) else 0)) := by
    classical
    ext i j
    by_cases hij : (i : Y) = j
    · exact False.elim (hdisj i i.2 (hij ▸ j.2))
    · simp [coordinateBlock, Matrix.toBlock_apply, hij, j.2]
  rw [heq]
  exact norm_coordinateBlock_le p q _

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

/-- Conjugation by a unitary transports a multiplication defect exactly. -/
theorem unitaryConjugation_mul_defect_eq
    {U A B C : Matrix Y Y ℂ} (hU : U * Uᴴ = 1) :
    Uᴴ * A * U - (Uᴴ * B * U) * (Uᴴ * C * U) =
      Uᴴ * (A - B * C) * U := by
  rw [show (Uᴴ * B * U) * (Uᴴ * C * U) =
      Uᴴ * B * (U * Uᴴ) * C * U by noncomm_ring, hU]
  noncomm_ring

/-! ## Weak-MF moving coordinates -/

section WeakMF

variable {G : Type} [Group G]

/-- The finite-stage Hermitian average, abbreviated for the moving-corner
definitions. -/
noncomputable def movingHermitianAverage (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) : Matrix (A.model n) (A.model n) ℂ :=
  hermitianAverage A S n

/-- The Hermitian proof used by the moving-coordinate type. -/
theorem movingHermitianAverage_isHermitian (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) :
    (movingHermitianAverage A S n).IsHermitian :=
  hermitianAverage_conjTranspose A S n

/-- Predicate cutting out the moving eigen-coordinates. -/
def movingPredicate (A : OpAlmostRepresentation G) (S : Finset G)
    (t : ℝ) (n : ℕ) (i : A.model n) : Prop :=
  (movingHermitianAverage_isHermitian A S n).eigenvalues i ≤ t

/-- Every eigen-coordinate belongs to the cutoff taken at its own eigenvalue;
this is a closed satisfiability witness for the moving-coordinate predicate. -/
theorem movingPredicate_at_eigenvalue (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) (i : A.model n) :
    movingPredicate A S
      ((movingHermitianAverage_isHermitian A S n).eigenvalues i) n i :=
  le_rfl

noncomputable instance movingPredicate_decidable (A : OpAlmostRepresentation G)
    (S : Finset G) (t : ℝ) (n : ℕ) :
    DecidablePred (movingPredicate A S t n) := Classical.decPred _

/-- The honest finite coordinate type of the moving spectral corner.  This is
kept irreducible so later matrix-instance synthesis does not repeatedly normalize the
full spectral theorem proof stored in its defining predicate. -/
noncomputable def WeakMFMovingIndex (A : OpAlmostRepresentation G) (S : Finset G)
    (t : ℝ) (n : ℕ) :=
  {i : A.model n // movingPredicate A S t n i}

noncomputable instance weakMFMovingIndexFintype (A : OpAlmostRepresentation G)
    (S : Finset G) (t : ℝ) (n : ℕ) :
    Fintype (WeakMFMovingIndex A S t n) := by
  unfold WeakMFMovingIndex
  infer_instance

noncomputable instance weakMFMovingIndexDecidableEq (A : OpAlmostRepresentation G)
    (S : Finset G) (t : ℝ) (n : ℕ) :
    DecidableEq (WeakMFMovingIndex A S t n) := Classical.decEq _

/-- Conjugate a microstate into the eigenbasis of the Hermitian average. -/
noncomputable def eigenbasisMicrostate (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) (g : G) :
    Matrix (A.model n) (A.model n) ℂ :=
  let U : Matrix (A.model n) (A.model n) ℂ :=
    (movingHermitianAverage_isHermitian A S n).eigenvectorUnitary
  Uᴴ * (A.map n g : Matrix (A.model n) (A.model n) ℂ) * U

/-- Eigenbasis conjugation preserves membership in the unitary group. -/
theorem eigenbasisMicrostate_mem_unitaryGroup (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) (g : G) :
    eigenbasisMicrostate A S n g ∈ Matrix.unitaryGroup (A.model n) ℂ := by
  let hH := movingHermitianAverage_isHermitian A S n
  let U : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup (A.model n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  change Uᴴ * (A.map n g : Matrix (A.model n) (A.model n) ℂ) * U ∈
    Matrix.unitaryGroup (A.model n) ℂ
  exact mul_mem (mul_mem hUstar (A.map n g).2) hH.eigenvectorUnitary.2

/-- The eigenbasis microstate has exact Gram matrix one. -/
theorem eigenbasisMicrostate_star_mul_self (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) (g : G) :
    (eigenbasisMicrostate A S n g)ᴴ * eigenbasisMicrostate A S n g = 1 := by
  have hunit := eigenbasisMicrostate_mem_unitaryGroup A S n g
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hunit
  exact hunit

/-- The multiplication defect in the Hermitian eigenbasis is the unitary
conjugate of the original weak-MF defect. -/
theorem eigenbasisMicrostate_mul_defect_eq (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) (g h : G) :
    eigenbasisMicrostate A S n (g * h) -
        eigenbasisMicrostate A S n g * eigenbasisMicrostate A S n h =
      let U : Matrix (A.model n) (A.model n) ℂ :=
        (movingHermitianAverage_isHermitian A S n).eigenvectorUnitary
      Uᴴ * ((A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) * A.map n h) * U := by
  let hH := movingHermitianAverage_isHermitian A S n
  let U : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
  have hU : U * Uᴴ = 1 :=
    Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  change Uᴴ * (A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) * U -
      (Uᴴ * (A.map n g : Matrix (A.model n) (A.model n) ℂ) * U) *
        (Uᴴ * (A.map n h : Matrix (A.model n) (A.model n) ℂ) * U) = _
  exact unitaryConjugation_mul_defect_eq hU

/-- Eigenbasis conjugation preserves the norm of the weak-MF
multiplication defect. -/
theorem norm_eigenbasisMicrostate_mul_defect_eq
    (A : OpAlmostRepresentation G) (S : Finset G) (n : ℕ) (g h : G) :
    ‖eigenbasisMicrostate A S n (g * h) -
        eigenbasisMicrostate A S n g * eigenbasisMicrostate A S n h‖ =
      ‖(A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) * A.map n h‖ := by
  let hH := movingHermitianAverage_isHermitian A S n
  let U : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup (A.model n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  rw [eigenbasisMicrostate_mul_defect_eq]
  simpa only [Matrix.conjTranspose_conjTranspose] using
    norm_unitary_conjugate hUstar
      (D := (A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          (A.map n h : Matrix (A.model n) (A.model n) ℂ))

/-- In its eigenbasis, the Hermitian average is the diagonal matrix of its
real eigenvalues. -/
theorem eigenbasis_movingHermitianAverage_eq_diagonal
    (A : OpAlmostRepresentation G) (S : Finset G) (n : ℕ) :
    let hH := movingHermitianAverage_isHermitian A S n
    let U : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
    Uᴴ * movingHermitianAverage A S n * U =
      Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) := by
  let hH := movingHermitianAverage_isHermitian A S n
  let U : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
  have hUU : Uᴴ * U = 1 :=
    Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hspec : movingHermitianAverage A S n =
      U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) * Uᴴ := by
    calc
      movingHermitianAverage A S n =
          Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
            (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) :=
        hH.spectral_theorem
      _ = U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) * Uᴴ := by
        rfl
  change Uᴴ * movingHermitianAverage A S n * U =
    Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ))
  calc
    Uᴴ * movingHermitianAverage A S n * U =
        Uᴴ * (U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) * Uᴴ) * U :=
      congrArg (fun H : Matrix (A.model n) (A.model n) ℂ ↦ Uᴴ * H * U) hspec
    _ =
        (Uᴴ * U) * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) *
          (Uᴴ * U) := by noncomm_ring
    _ = Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) := by
      rw [hUU, Matrix.one_mul, Matrix.mul_one]

/-- The weak-MF orbit average written in the Hermitian eigenbasis. -/
noncomputable def eigenbasisAverage (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) : Matrix (A.model n) (A.model n) ℂ :=
  ((S.card : ℂ)⁻¹) • ∑ g ∈ S, eigenbasisMicrostate A S n g

/-- Conjugating the original orbit average gives the average of the
conjugated microstates. -/
theorem eigenbasisAverage_eq (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) :
    let U : Matrix (A.model n) (A.model n) ℂ :=
      (movingHermitianAverage_isHermitian A S n).eigenvectorUnitary
    eigenbasisAverage A S n = Uᴴ * matrixAverage A S n * U := by
  let U : Matrix (A.model n) (A.model n) ℂ :=
    (movingHermitianAverage_isHermitian A S n).eigenvectorUnitary
  change ((S.card : ℂ)⁻¹) • ∑ g ∈ S,
      Uᴴ * (A.map n g : Matrix (A.model n) (A.model n) ℂ) * U =
    Uᴴ * (((S.card : ℂ)⁻¹) •
      (∑ g ∈ S, (A.map n g : Matrix (A.model n) (A.model n) ℂ))) * U
  rw [Matrix.mul_smul, Matrix.smul_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]

/-- The Hermitian average in its eigenbasis is the exact Hermitian
symmetrization of `eigenbasisAverage`. -/
theorem eigenbasis_movingHermitianAverage_eq_symmetrized
    (A : OpAlmostRepresentation G) (S : Finset G) (n : ℕ) :
    let hH := movingHermitianAverage_isHermitian A S n
    let U : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
    Uᴴ * movingHermitianAverage A S n * U =
      (2 : ℂ)⁻¹ • (eigenbasisAverage A S n + (eigenbasisAverage A S n)ᴴ) := by
  let hH := movingHermitianAverage_isHermitian A S n
  let U : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
  have hE : eigenbasisAverage A S n = Uᴴ * matrixAverage A S n * U := by
    simpa only using eigenbasisAverage_eq A S n
  change Uᴴ * ((2 : ℂ)⁻¹ •
      (matrixAverage A S n + (matrixAverage A S n)ᴴ)) * U = _
  rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hE, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  noncomm_ring

/-- Each Hermitian-average eigenvalue is the average real diagonal entry of
the conjugated microstates. -/
theorem movingEigenvalue_eq_average_re (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) (i : A.model n) :
    (movingHermitianAverage_isHermitian A S n).eigenvalues i =
      ((S.card : ℝ)⁻¹) * ∑ g ∈ S, (eigenbasisMicrostate A S n g i i).re := by
  let hH := movingHermitianAverage_isHermitian A S n
  have hdiag := eigenbasis_movingHermitianAverage_eq_diagonal A S n
  have hsym := eigenbasis_movingHermitianAverage_eq_symmetrized A S n
  have hmatrix : Matrix.diagonal (fun j ↦ (hH.eigenvalues j : ℂ)) =
      (2 : ℂ)⁻¹ • (eigenbasisAverage A S n + (eigenbasisAverage A S n)ᴴ) :=
    hdiag.symm.trans hsym
  have hii := congrArg (fun M : Matrix (A.model n) (A.model n) ℂ ↦ M i i) hmatrix
  have hre := congrArg Complex.re hii
  simp [eigenbasisAverage] at hre
  rw [Matrix.sum_apply i i S (fun g ↦ eigenbasisMicrostate A S n g),
    Complex.re_sum] at hre
  ring_nf at hre
  simpa only [hH] using hre

/-- Clearing the nonzero generator-cardinality denominator in the preceding
eigenvalue identity. -/
theorem sum_re_eigenbasisMicrostate_diagonal_eq
    (A : OpAlmostRepresentation G) (S : Finset G) (hone : 1 ∈ S)
    (n : ℕ) (i : A.model n) :
    ∑ g ∈ S, (eigenbasisMicrostate A S n g i i).re =
      (S.card : ℝ) *
        (movingHermitianAverage_isHermitian A S n).eigenvalues i := by
  rw [movingEigenvalue_eq_average_re A S n i]
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨1, hone⟩
  field_simp

/-- The canonical finite model carried by the moving coordinate subtype. -/
noncomputable abbrev weakMFMovingModel (A : OpAlmostRepresentation G)
    (S : Finset G) (t : ℝ) (n : ℕ) : FiniteModel :=
  ⟨{i : A.model n // movingPredicate A S t n i}, inferInstance,
    inferInstance⟩

/-- Real normalized trace is the average of the real diagonal entries. -/
theorem re_normTrace_eq_average_diagonal (Y : FiniteModel)
    (C : Matrix Y Y ℂ) :
    (normTrace Y C).re =
      ((Fintype.card Y : ℝ)⁻¹) * ∑ i : Y, (C i i).re := by
  simp only [normTrace, Matrix.trace, div_eq_mul_inv, Complex.mul_re,
    Complex.re_sum, Complex.inv_re, Complex.inv_im, Complex.natCast_re,
    Complex.natCast_im, Complex.normSq_natCast, Matrix.diag_apply]
  by_cases hcard : (Fintype.card Y : ℝ) = 0
  · simp [hcard]
  · field_simp
    ring

/-- Normalized trace is contractive for the matrix `ℓ²` operator norm. -/
theorem norm_normTrace_le_l2_opNorm (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) (C : Matrix Y Y ℂ) :
    ‖normTrace Y C‖ ≤ ‖C‖ := by
  have hentry (i : Y) : ‖C i i‖ ≤ ‖C‖ := by
    have hs := normSq_entry_le_sq_l2_opNorm Y C i i
    rw [Complex.normSq_eq_norm_sq] at hs
    nlinarith [norm_nonneg (C i i), norm_nonneg C]
  have htrace : ‖Matrix.trace C‖ ≤ (Fintype.card Y : ℝ) * ‖C‖ := by
    calc
      ‖Matrix.trace C‖ = ‖∑ i : Y, C i i‖ := rfl
      _ ≤ ∑ i : Y, ‖C i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Y, ‖C‖ := Finset.sum_le_sum fun i _ ↦ hentry i
      _ = (Fintype.card Y : ℝ) * ‖C‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  rw [normTrace, norm_div, Complex.norm_natCast, div_le_iff₀ hcard]
  simpa only [mul_comm] using htrace

/-- The real normalized trace changes by at most the operator norm of a
matrix perturbation. -/
theorem re_normTrace_le_add_l2_opNorm (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) (W C : Matrix Y Y ℂ) :
    (normTrace Y W).re ≤ (normTrace Y C).re + ‖W - C‖ := by
  have hre : (normTrace Y W - normTrace Y C).re ≤
      ‖normTrace Y W - normTrace Y C‖ := Complex.re_le_norm _
  change (normTrace Y W).re - (normTrace Y C).re ≤
    ‖normTrace Y W - normTrace Y C‖ at hre
  have hnorm : ‖normTrace Y W - normTrace Y C‖ ≤ ‖W - C‖ := by
    rw [← normTrace_sub]
    exact norm_normTrace_le_l2_opNorm Y hY (W - C)
  linarith

/-- Principal compression of a weak-MF microstate to the moving eigenspace. -/
noncomputable def movingCompression (A : OpAlmostRepresentation G)
    (S : Finset G) (t : ℝ) (n : ℕ) (g : G) :
    Matrix {i : A.model n // movingPredicate A S t n i}
      {i : A.model n // movingPredicate A S t n i} ℂ :=
  principalBlock
    (movingPredicate A S t n)
    (eigenbasisMicrostate A S n g)

/-- The average real normalized trace of the moving generator blocks is at
most the spectral cutoff. -/
theorem sum_re_normTrace_movingCompression_le
    (A : OpAlmostRepresentation G) (S : Finset G) (hone : 1 ∈ S)
    (t : ℝ) (n : ℕ)
    (hY : Nonempty {i : A.model n // movingPredicate A S t n i}) :
    ∑ g ∈ S, (normTrace (weakMFMovingModel A S t n)
      (movingCompression A S t n g)).re ≤ (S.card : ℝ) * t := by
  classical
  let Y := weakMFMovingModel A S t n
  have hcardY : 0 < Fintype.card Y := Fintype.card_pos_iff.mpr hY
  have hpoint (i : Y) :
      ∑ g ∈ S, (movingCompression A S t n g i i).re ≤
        (S.card : ℝ) * t := by
    have heq := sum_re_eigenbasisMicrostate_diagonal_eq A S hone n (i : A.model n)
    have hi : (movingHermitianAverage_isHermitian A S n).eigenvalues i ≤ t :=
      i.2
    simp only [movingCompression, principalBlock, coordinateBlock,
      Matrix.toBlock_apply] at ⊢
    rw [heq]
    exact mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)
  have hsum :
      ∑ i : Y, ∑ g ∈ S, (movingCompression A S t n g i i).re ≤
        ∑ _i : Y, (S.card : ℝ) * t :=
    Finset.sum_le_sum fun i _ ↦ hpoint i
  simp_rw [re_normTrace_eq_average_diagonal]
  rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    ((Fintype.card Y : ℝ)⁻¹) *
        ∑ i : Y, ∑ g ∈ S, (movingCompression A S t n g i i).re ≤
      ((Fintype.card Y : ℝ)⁻¹) *
        ∑ _i : Y, (S.card : ℝ) * t :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = (S.card : ℝ) * t := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast hcardY.ne'
      field_simp

/-- In the Hermitian eigenbasis, the residual on the top coordinates is
unitarily conjugate to `topSpectralDisplacement`. -/
theorem eigenbasis_top_residual_eq (A : OpAlmostRepresentation G)
    (S : Finset G) (t : ℝ) (n : ℕ) (g : G) :
    (eigenbasisMicrostate A S n g - 1) *
        Matrix.diagonal (fun i ↦
          if ¬movingPredicate A S t n i then (1 : ℂ) else 0) =
      let U : Matrix (A.model n) (A.model n) ℂ :=
        (movingHermitianAverage_isHermitian A S n).eigenvectorUnitary
      Uᴴ * topSpectralDisplacement A S t n g * U := by
  classical
  let hH := movingHermitianAverage_isHermitian A S n
  let U : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
  let D : Matrix (A.model n) (A.model n) ℂ :=
    Matrix.diagonal (fun i ↦ if t < hH.eigenvalues i then 1 else 0)
  have hUU : Uᴴ * U = 1 :=
    Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hUUD : Uᴴ * (U * D) = D := by
    rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  simp only [eigenbasisMicrostate, topSpectralDisplacement, spectralAbove,
    movingPredicate, movingHermitianAverage, not_le]
  change (Uᴴ * (A.map n g : Matrix (A.model n) (A.model n) ℂ) * U - 1) *
      D = Uᴴ * (((A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1) *
        (U * D * Uᴴ)) * U
  symm
  calc
    Uᴴ * (((A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1) *
        (U * D * Uᴴ)) * U =
      Uᴴ * ((A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1) *
        U * D * (Uᴴ * U) := by noncomm_ring
    _ = Uᴴ * ((A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1) *
        U * D := by rw [hUU, Matrix.mul_one]
    _ = (Uᴴ * (A.map n g : Matrix (A.model n) (A.model n) ℂ) * U - 1) *
        D := by
      rw [show Uᴴ * ((A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1) *
          U * D = Uᴴ * (A.map n g : Matrix (A.model n) (A.model n) ℂ) * U * D -
            Uᴴ * (U * D) by noncomm_ring, hUUD]
      noncomm_ring

/-- The moving-to-top off-diagonal block is controlled by the already
formalized top displacement. -/
theorem norm_movingToTopBlock_le (A : OpAlmostRepresentation G)
    (S : Finset G) (t : ℝ) (n : ℕ) (g : G) :
    ‖coordinateBlock (movingPredicate A S t n)
        (fun i ↦ ¬movingPredicate A S t n i)
        (eigenbasisMicrostate A S n g)‖ ≤
      ‖topSpectralDisplacement A S t n g‖ := by
  classical
  let hH := movingHermitianAverage_isHermitian A S n
  let U : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup (A.model n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  calc
    ‖coordinateBlock (movingPredicate A S t n)
        (fun i ↦ ¬movingPredicate A S t n i)
        (eigenbasisMicrostate A S n g)‖ ≤
      ‖(eigenbasisMicrostate A S n g - 1) *
        Matrix.diagonal (fun i ↦
          if ¬movingPredicate A S t n i then (1 : ℂ) else 0)‖ :=
      norm_coordinateBlock_disjoint_le_residual _ _
        (fun i hi hni ↦ hni hi) _
    _ = ‖Uᴴ * topSpectralDisplacement A S t n g * U‖ := by
      rw [eigenbasis_top_residual_eq]
    _ = ‖topSpectralDisplacement A S t n g‖ := by
      simpa only [Matrix.conjTranspose_conjTranspose] using
        norm_unitary_conjugate hUstar
          (D := topSpectralDisplacement A S t n g)

/-- The opposite off-diagonal block is controlled by the inverse top
displacement, up to the weak-MF inverse defect. -/
theorem norm_topToMovingBlock_le (A : OpAlmostRepresentation G)
    (S : Finset G) (t : ℝ) (n : ℕ) (g : G) :
    ‖coordinateBlock (fun i ↦ ¬movingPredicate A S t n i)
        (movingPredicate A S t n)
        (eigenbasisMicrostate A S n g)‖ ≤
      ‖topSpectralDisplacement A S t n g⁻¹‖ +
        ‖(A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ‖ := by
  classical
  let hH := movingHermitianAverage_isHermitian A S n
  let U : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
  let Vstar : Matrix (A.model n) (A.model n) ℂ :=
    (eigenbasisMicrostate A S n g)ᴴ
  let Vinv : Matrix (A.model n) (A.model n) ℂ :=
    eigenbasisMicrostate A S n g⁻¹
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup (A.model n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hblockStar :
      ‖coordinateBlock (fun i ↦ ¬movingPredicate A S t n i)
          (movingPredicate A S t n) (eigenbasisMicrostate A S n g)‖ =
        ‖coordinateBlock (movingPredicate A S t n)
          (fun i ↦ ¬movingPredicate A S t n i) Vstar‖ := by
    rw [← coordinateBlock_conjTranspose]
    exact (Matrix.l2_opNorm_conjTranspose
      (coordinateBlock (fun i ↦ ¬movingPredicate A S t n i)
        (movingPredicate A S t n) (eigenbasisMicrostate A S n g))).symm
  have hdiff : Vstar - Vinv =
      Uᴴ * ((A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ -
        (A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ)) * U := by
    simp only [Vstar, Vinv, eigenbasisMicrostate, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    noncomm_ring
  have hnormdiff : ‖Uᴴ *
      ((A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ -
        (A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ)) * U‖ =
      ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ -
        (A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ)‖ := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      norm_unitary_conjugate hUstar
        (D := (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ -
          (A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ))
  rw [hblockStar]
  have hsplit : coordinateBlock (movingPredicate A S t n)
      (fun i ↦ ¬movingPredicate A S t n i) Vstar =
      coordinateBlock (movingPredicate A S t n)
          (fun i ↦ ¬movingPredicate A S t n i) Vinv +
        coordinateBlock (movingPredicate A S t n)
          (fun i ↦ ¬movingPredicate A S t n i) (Vstar - Vinv) := by
    ext i j
    simp [coordinateBlock, Matrix.toBlock_apply]
  rw [hsplit]
  calc
    ‖coordinateBlock (movingPredicate A S t n)
          (fun i ↦ ¬movingPredicate A S t n i) Vinv +
        coordinateBlock (movingPredicate A S t n)
          (fun i ↦ ¬movingPredicate A S t n i) (Vstar - Vinv)‖ ≤
      ‖coordinateBlock (movingPredicate A S t n)
          (fun i ↦ ¬movingPredicate A S t n i) Vinv‖ +
        ‖coordinateBlock (movingPredicate A S t n)
          (fun i ↦ ¬movingPredicate A S t n i) (Vstar - Vinv)‖ :=
      norm_add_le _ _
    _ ≤ ‖topSpectralDisplacement A S t n g⁻¹‖ + ‖Vstar - Vinv‖ :=
      add_le_add (norm_movingToTopBlock_le A S t n g⁻¹)
        (norm_coordinateBlock_le _ _ _)
    _ = ‖topSpectralDisplacement A S t n g⁻¹‖ +
        ‖(A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ‖ := by
      rw [hdiff, hnormdiff, show
        (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ - A.map n g⁻¹ =
          -((A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ) -
            (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) by abel,
        norm_neg]

/-- Both off-diagonal blocks vanish for every group element. -/
theorem offDiagonalBlocks_eventually_small_of_generates
    {Q : Finset G} {epsilon : ℝ}
    (hQ : IsKazhdanPair.{0, 0} G Q epsilon)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S)
    (hepsilonOne : epsilon ≤ 1) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (A : OpAlmostRepresentation G) {t : ℝ}
    (ht : 1 - epsilon ^ 2 / (4 * S.card) < t) (g : G) :
    ∀ eta : ℝ, 0 < eta → ∃ N, ∀ n ≥ N,
      ‖coordinateBlock (movingPredicate A S t n)
          (fun i ↦ ¬movingPredicate A S t n i)
          (eigenbasisMicrostate A S n g)‖ ≤ eta ∧
      ‖coordinateBlock (fun i ↦ ¬movingPredicate A S t n i)
          (movingPredicate A S t n)
          (eigenbasisMicrostate A S n g)‖ ≤ eta := by
  intro eta heta
  have hdisp (k : G) := topSpectralDisplacement_vanishing_of_generates
    hQ S hQS hone hepsilonOne hsymm hgen A ht k
  obtain ⟨Ng, hNg⟩ := hdisp g eta heta
  obtain ⟨Ni, hNi⟩ := hdisp g⁻¹ (eta / 2) (by linarith)
  obtain ⟨Nv, hNv⟩ := map_inv_vanishing A g (eta / 2) (by linarith)
  refine ⟨max Ng (max Ni Nv), fun n hn ↦ ⟨?_, ?_⟩⟩
  · exact (norm_movingToTopBlock_le A S t n g).trans
      (hNg n ((le_max_left _ _).trans hn))
  · calc
      ‖coordinateBlock (fun i ↦ ¬movingPredicate A S t n i)
          (movingPredicate A S t n) (eigenbasisMicrostate A S n g)‖ ≤
        ‖topSpectralDisplacement A S t n g⁻¹‖ +
          ‖(A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ) -
            (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ‖ :=
        norm_topToMovingBlock_le A S t n g
      _ ≤ eta / 2 + eta / 2 := add_le_add
        (hNi n (le_trans (le_trans (le_max_left Ni Nv)
          (le_max_right Ng (max Ni Nv))) hn))
        (hNv n (le_trans (le_trans (le_max_right Ni Nv)
          (le_max_right Ng (max Ni Nv))) hn))
      _ = eta := by ring

/-- Eigenbasis conjugation preserves the norm-one property of a microstate. -/
theorem norm_eigenbasisMicrostate_eq_one (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) (g : G) :
    ‖eigenbasisMicrostate A S n g‖ = 1 := by
  letI : Nonempty (A.model n) :=
    Fintype.card_pos_iff.mp (A.modelNonempty n)
  exact CStarRing.norm_of_mem_unitary
    (eigenbasisMicrostate_mem_unitaryGroup A S n g)

/-- Pointwise multiplicativity estimate for the uncorrected moving
compression. -/
theorem norm_movingCompression_mul_defect_le
    (A : OpAlmostRepresentation G) (S : Finset G) (t : ℝ)
    (n : ℕ) (g h : G) :
    ‖movingCompression A S t n (g * h) -
        movingCompression A S t n g * movingCompression A S t n h‖ ≤
      ‖(A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) * A.map n h‖ +
      ‖coordinateBlock (movingPredicate A S t n)
        (fun i ↦ ¬movingPredicate A S t n i)
        (eigenbasisMicrostate A S n g)‖ *
      ‖coordinateBlock (fun i ↦ ¬movingPredicate A S t n i)
        (movingPredicate A S t n)
        (eigenbasisMicrostate A S n h)‖ := by
  classical
  have hbound := norm_principalBlock_mul_defect_le
    (movingPredicate A S t n)
    (eigenbasisMicrostate A S n (g * h))
    (eigenbasisMicrostate A S n g)
    (eigenbasisMicrostate A S n h)
  rw [norm_eigenbasisMicrostate_mul_defect_eq A S n g h] at hbound
  exact hbound

/-- The uncorrected moving compressions are asymptotically multiplicative in
operator norm. -/
theorem movingCompression_multiplicative_eventually
    {Q : Finset G} {epsilon : ℝ}
    (hQ : IsKazhdanPair.{0, 0} G Q epsilon)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S)
    (hepsilonOne : epsilon ≤ 1) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (A : OpAlmostRepresentation G) {t : ℝ}
    (ht : 1 - epsilon ^ 2 / (4 * S.card) < t) (g h : G) :
    ∀ eta : ℝ, 0 < eta → ∃ N, ∀ n ≥ N,
      ‖movingCompression A S t n (g * h) -
        movingCompression A S t n g * movingCompression A S t n h‖ ≤ eta := by
  intro eta heta
  obtain ⟨Nm, hNm⟩ := A.asymptoticallyMultiplicative g h (eta / 2) (by linarith)
  obtain ⟨No, hNo⟩ := offDiagonalBlocks_eventually_small_of_generates
    hQ S hQS hone hepsilonOne hsymm hgen A ht g (eta / 2) (by linarith)
  refine ⟨max Nm No, fun n hn ↦ ?_⟩
  have hright : ‖coordinateBlock (fun i ↦ ¬movingPredicate A S t n i)
      (movingPredicate A S t n) (eigenbasisMicrostate A S n h)‖ ≤ 1 := by
    exact (norm_coordinateBlock_le _ _ _).trans_eq
      (norm_eigenbasisMicrostate_eq_one A S n h)
  calc
    ‖movingCompression A S t n (g * h) -
        movingCompression A S t n g * movingCompression A S t n h‖ ≤
      ‖(A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) * A.map n h‖ +
      ‖coordinateBlock (movingPredicate A S t n)
        (fun i ↦ ¬movingPredicate A S t n i) (eigenbasisMicrostate A S n g)‖ *
      ‖coordinateBlock (fun i ↦ ¬movingPredicate A S t n i)
        (movingPredicate A S t n) (eigenbasisMicrostate A S n h)‖ :=
      norm_movingCompression_mul_defect_le A S t n g h
    _ ≤ eta / 2 + (eta / 2) * 1 := add_le_add
      (hNm n ((le_max_left _ _).trans hn))
      (mul_le_mul (hNo n ((le_max_right _ _).trans hn)).1 hright
        (norm_nonneg _) (by linarith))
    _ = eta := by ring

/-- Pointwise Gram-defect estimate for the moving compression. -/
theorem norm_movingCompression_gram_sub_one_le
    (A : OpAlmostRepresentation G) (S : Finset G) (t : ℝ)
    (n : ℕ) (g : G) :
    ‖cornerGram (movingCompression A S t n g) - 1‖ ≤
      ‖coordinateBlock (fun i ↦ ¬movingPredicate A S t n i)
        (movingPredicate A S t n) (eigenbasisMicrostate A S n g)‖ ^ 2 := by
  classical
  exact norm_principalBlock_gram_sub_one_le
    (movingPredicate A S t n) (eigenbasisMicrostate A S n g)
      (eigenbasisMicrostate_star_mul_self A S n g)

/-- A moving compression is a contraction. -/
theorem norm_movingCompression_le_one (A : OpAlmostRepresentation G)
    (S : Finset G) (t : ℝ) (n : ℕ) (g : G) :
    ‖movingCompression A S t n g‖ ≤ 1 := by
  classical
  exact (norm_principalBlock_le (movingPredicate A S t n)
    (eigenbasisMicrostate A S n g)).trans_eq
      (norm_eigenbasisMicrostate_eq_one A S n g)

/-- Exact unitary obtained by polar-correcting a good moving compression. -/
noncomputable def polarCorrectedMovingCompression
    (A : OpAlmostRepresentation G) (S : Finset G) (t : ℝ)
    (n : ℕ) (g : G) {delta : ℝ} (hdeltaHalf : delta ≤ 1 / 2)
    (hclose : ‖cornerGram (movingCompression A S t n g) - 1‖ ≤ delta) :
    Matrix.unitaryGroup {i : A.model n // movingPredicate A S t n i} ℂ :=
  polarCorrectUnitary (movingCompression A S t n g)
    (cornerGram_isHermitian _) hdeltaHalf hclose

/-- Polar correction moves a good compression by at most twice its Gram
defect bound. -/
theorem norm_polarCorrectedMovingCompression_sub_le
    (A : OpAlmostRepresentation G) (S : Finset G) (t : ℝ)
    (n : ℕ) (g : G) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hdeltaHalf : delta ≤ 1 / 2)
    (hclose : ‖cornerGram (movingCompression A S t n g) - 1‖ ≤ delta) :
    ‖(polarCorrectedMovingCompression A S t n g hdeltaHalf hclose :
        Matrix {i : A.model n // movingPredicate A S t n i}
          {i : A.model n // movingPredicate A S t n i} ℂ) -
      movingCompression A S t n g‖ ≤ 2 * delta := by
  exact norm_polarCorrect_sub_le (movingCompression A S t n g)
    (cornerGram_isHermitian _) (norm_movingCompression_le_one A S t n g)
      hdelta hdeltaHalf hclose

/-- Gram defects of all fixed compressed elements vanish. -/
theorem movingCompression_gram_eventually_small
    {Q : Finset G} {epsilon : ℝ}
    (hQ : IsKazhdanPair.{0, 0} G Q epsilon)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S)
    (hepsilonOne : epsilon ≤ 1) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (A : OpAlmostRepresentation G) {t : ℝ}
    (ht : 1 - epsilon ^ 2 / (4 * S.card) < t) (g : G) :
    ∀ eta : ℝ, 0 < eta → ∃ N, ∀ n ≥ N,
      ‖cornerGram (movingCompression A S t n g) - 1‖ ≤ eta := by
  intro eta heta
  obtain ⟨N, hN⟩ := offDiagonalBlocks_eventually_small_of_generates
    hQ S hQS hone hepsilonOne hsymm hgen A ht g (Real.sqrt eta)
      (Real.sqrt_pos.2 heta)
  refine ⟨N, fun n hn ↦ (norm_movingCompression_gram_sub_one_le A S t n g).trans ?_⟩
  have hb := (hN n hn).2
  nlinarith [norm_nonneg (coordinateBlock
    (fun i ↦ ¬movingPredicate A S t n i) (movingPredicate A S t n)
    (eigenbasisMicrostate A S n g)), Real.sq_sqrt heta.le]

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

/-- The moving corner is eventually nonzero.  If it vanished at arbitrarily
late stages, the top cutoff would be the identity there; all-element top
displacement and the identity defect would then contradict weak-MF
separation. -/
theorem eventually_nonempty_weakMFMovingIndex [Nontrivial G]
    {Q : Finset G} {epsilon : ℝ}
    (hQ : IsKazhdanPair.{0, 0} G Q epsilon)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S)
    (hepsilonOne : epsilon ≤ 1) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (A : WeakMFApproximation G) {t : ℝ}
    (ht : 1 - epsilon ^ 2 / (4 * S.card) < t) :
    ∃ N, ∀ n ≥ N,
      Nonempty (WeakMFMovingIndex A.toOpAlmostRepresentation S t n) := by
  classical
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hg1 : g ≠ 1 := hg
  have hdisp := topSpectralDisplacement_vanishing_of_generates
    hQ S hQS hone hepsilonOne hsymm hgen A.toOpAlmostRepresentation ht g
  obtain ⟨Nd, hNd⟩ := hdisp (A.separation / 4) (by
    linarith [A.separation_pos])
  obtain ⟨N1, hN1⟩ := map_one_vanishing A.toOpAlmostRepresentation (A.separation / 4) (by
    linarith [A.separation_pos])
  obtain ⟨Ns, hNs⟩ := A.separatedEventually g 1 hg1
  refine ⟨max (max Nd N1) Ns, fun n hn ↦ ?_⟩
  by_contra hempty
  have hall : ∀ i : A.model n,
      t < (movingHermitianAverage_isHermitian A.toOpAlmostRepresentation S n).eigenvalues i := by
    intro i
    exact lt_of_not_ge fun hi ↦
      hempty ⟨⟨i, hi⟩⟩
  have hP : spectralAbove (hermitianAverage A.toOpAlmostRepresentation S n)
      (hermitianAverage_conjTranspose A.toOpAlmostRepresentation S n) t = 1 :=
    spectralAbove_eq_one_of_forall_lt _ _ _ hall
  have hNdle : Nd ≤ n :=
    (le_max_left Nd N1).trans (le_max_left (max Nd N1) Ns) |>.trans hn
  have hN1le : N1 ≤ n :=
    (le_max_right Nd N1).trans (le_max_left (max Nd N1) Ns) |>.trans hn
  have hd := hNd n hNdle
  have h1 := hN1 n hN1le
  have hs := hNs n ((le_max_right _ _).trans hn)
  change ‖((A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1) *
    spectralAbove (hermitianAverage A.toOpAlmostRepresentation S n)
      (hermitianAverage_conjTranspose A.toOpAlmostRepresentation S n) t‖ ≤ A.separation / 4 at hd
  rw [hP, Matrix.mul_one] at hd
  have hcontra : A.separation < A.separation := calc
    A.separation ≤
        ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ) - A.map n 1‖ := hs
    _ ≤ ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1‖ +
          ‖(A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1‖ := by
      rw [show (A.map n g : Matrix (A.model n) (A.model n) ℂ) - A.map n 1 =
        ((A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1) -
          ((A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1) by abel]
      exact norm_sub_le _ _
    _ ≤ A.separation / 4 + A.separation / 4 := add_le_add hd h1
    _ < A.separation := by linarith [A.separation_pos]
  exact (lt_irrefl _ hcontra)

end WeakMF

end KazhdanCornerMatrices
end GroupApproximation
