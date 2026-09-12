import GroupApproximation.Sofic.HyperlinearAmplification
import GroupApproximation.Sofic.KazhdanCornerModel
import GroupApproximation.Sofic.OpAlmostRepresentation

/-!
# Finite adjoint representations

For a matrix `U` on `Y`, `conjDouble U` is the matrix of the conjugation
operator `X ↦ U * X * Uᴴ` after arranging the entries of `X` in row-major
order.  The existing tensor-double API supplies exact multiplicativity and
unitarity.  This file adds the dimension-free perturbation estimate

`|‖Ad(U) - Ad(V)‖| ≤ 2 |‖U - V‖|`

for unitary `U,V`, and packages the construction as an operator-norm almost
representation on the matrix Hilbert spaces.
-/

namespace GroupApproximation

open Matrix KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

universe u

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- Row-major vectorization, matching the coordinate convention of
`conjDouble`. -/
@[simp] def rowVec (X : Matrix Y Y ℂ) : Y × Y → ℂ :=
  fun ij ↦ X ij.1 ij.2

/-- A pair-coordinate vector viewed as a matrix, inverse to `rowVec`. -/
@[simp] def rowMat (x : Y × Y → ℂ) : Matrix Y Y ℂ :=
  Matrix.of fun i j ↦ x (i, j)

omit [Fintype Y] [DecidableEq Y] in
theorem rowVec_rowMat (x : Y × Y → ℂ) : rowVec (rowMat x) = x := by
  funext p
  simp

omit [DecidableEq Y] in
/-- `conjDouble U` acts on row-vectorized matrices by conjugation. -/
theorem conjDouble_mulVec_rowVec (U X : Matrix Y Y ℂ) :
    conjDouble U *ᵥ rowVec X = rowVec (U * X * Uᴴ) := by
  ext p
  simp only [Matrix.mulVec, dotProduct, conjDouble_apply, rowVec,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  change U p.1 j * (starRingEnd ℂ) (U p.2 i) * X j i =
    U p.1 j * X j i * (starRingEnd ℂ) (U p.2 i)
  ring

/-! ## Frobenius mass under vectorization -/

omit [DecidableEq Y] in
/-- Row-vectorized squared Euclidean mass is the Frobenius mass. -/
theorem sum_normSq_rowVec (X : Matrix Y Y ℂ) :
    ∑ p : Y × Y, Complex.normSq (rowVec X p) =
      ∑ i : Y, ∑ j : Y, Complex.normSq (X i j) := by
  rw [Fintype.sum_prod_type]
  rfl

omit [DecidableEq Y] in
/-- Frobenius mass is invariant under conjugate transpose. -/
theorem sum_normSq_conjTranspose (X : Matrix Y Y ℂ) :
    ∑ i : Y, ∑ j : Y, Complex.normSq (Xᴴ i j) =
      ∑ i : Y, ∑ j : Y, Complex.normSq (X i j) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp [Matrix.conjTranspose_apply]

/-- Left multiplication contracts Frobenius mass by the operator norm. -/
theorem sum_normSq_mul_left_le (A X : Matrix Y Y ℂ) :
    ∑ i : Y, ∑ j : Y, Complex.normSq ((A * X) i j) ≤
      ‖A‖ ^ 2 * ∑ i : Y, ∑ j : Y, Complex.normSq (X i j) := by
  rw [Finset.sum_comm (γ := Y) (s := Finset.univ) (t := Finset.univ)
    (f := fun i j ↦ Complex.normSq ((A * X) i j))]
  rw [Finset.sum_comm (γ := Y) (s := Finset.univ) (t := Finset.univ)
    (f := fun i j ↦ Complex.normSq (X i j))]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  have hcol : ∀ i : Y, (A * X) i j = (A *ᵥ fun k ↦ X k j) i := by
    intro i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  calc
    ∑ i : Y, Complex.normSq ((A * X) i j) =
        ∑ i : Y, Complex.normSq ((A *ᵥ fun k ↦ X k j) i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hcol i]
    _ ≤ ‖A‖ ^ 2 * ∑ i : Y, Complex.normSq (X i j) :=
      sum_normSq_mulVec_le_general A _

/-- Right multiplication contracts Frobenius mass by the operator norm. -/
theorem sum_normSq_mul_right_le (X B : Matrix Y Y ℂ) :
    ∑ i : Y, ∑ j : Y, Complex.normSq ((X * B) i j) ≤
      ‖B‖ ^ 2 * ∑ i : Y, ∑ j : Y, Complex.normSq (X i j) := by
  have hct : ∑ i : Y, ∑ j : Y, Complex.normSq ((X * B) i j) =
      ∑ i : Y, ∑ j : Y, Complex.normSq ((Bᴴ * Xᴴ) i j) := by
    rw [← sum_normSq_conjTranspose (X * B), Matrix.conjTranspose_mul]
  rw [hct]
  calc
    ∑ i : Y, ∑ j : Y, Complex.normSq ((Bᴴ * Xᴴ) i j) ≤
        ‖Bᴴ‖ ^ 2 * ∑ i : Y, ∑ j : Y, Complex.normSq (Xᴴ i j) :=
      sum_normSq_mul_left_le Bᴴ Xᴴ
    _ = ‖B‖ ^ 2 * ∑ i : Y, ∑ j : Y, Complex.normSq (X i j) := by
      rw [sum_normSq_conjTranspose, ← Matrix.star_eq_conjTranspose,
        norm_star]

/-! ## The mixed conjugation kernel -/

/-- The kernel `X ↦ A X Bᴴ` on row-major pair coordinates.  It specializes
to `conjDouble` on the diagonal `A = B` and linearizes differences of
conjugations. -/
def conjMixed (A B : Matrix Y Y ℂ) : Matrix (Y × Y) (Y × Y) ℂ :=
  fun p q ↦ A p.1 q.1 * (starRingEnd ℂ) (B p.2 q.2)

omit [Fintype Y] [DecidableEq Y] in
@[simp] theorem conjMixed_apply (A B : Matrix Y Y ℂ) (p q : Y × Y) :
    conjMixed A B p q = A p.1 q.1 * (starRingEnd ℂ) (B p.2 q.2) := rfl

omit [Fintype Y] [DecidableEq Y] in
theorem conjMixed_self (A : Matrix Y Y ℂ) : conjMixed A A = conjDouble A := by
  ext p q
  simp

omit [DecidableEq Y] in
/-- The mixed kernel acts on row-vectorized matrices as `X ↦ A X Bᴴ`. -/
theorem conjMixed_mulVec_rowVec (A B X : Matrix Y Y ℂ) :
    conjMixed A B *ᵥ rowVec X = rowVec (A * X * Bᴴ) := by
  ext p
  simp only [Matrix.mulVec, dotProduct, conjMixed_apply, rowVec,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  change A p.1 j * (starRingEnd ℂ) (B p.2 i) * X j i =
    A p.1 j * X j i * (starRingEnd ℂ) (B p.2 i)
  ring

/-- The mixed kernel is bounded by the product of the operator norms,
independently of the dimension. -/
theorem l2_opNorm_conjMixed_le (A B : Matrix Y Y ℂ) :
    ‖conjMixed A B‖ ≤ ‖A‖ * ‖B‖ := by
  refine l2_opNorm_le_of_sum_normSq_general _
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun x ↦ ?_
  have hx : x = rowVec (rowMat x) := (rowVec_rowMat x).symm
  rw [hx, conjMixed_mulVec_rowVec, sum_normSq_rowVec, sum_normSq_rowVec]
  calc
    ∑ i : Y, ∑ j : Y, Complex.normSq ((A * rowMat x * Bᴴ) i j) ≤
        ‖Bᴴ‖ ^ 2 * ∑ i : Y, ∑ j : Y, Complex.normSq ((A * rowMat x) i j) :=
      sum_normSq_mul_right_le _ _
    _ ≤ ‖Bᴴ‖ ^ 2 * (‖A‖ ^ 2 *
        ∑ i : Y, ∑ j : Y, Complex.normSq (rowMat x i j)) := by
      refine mul_le_mul_of_nonneg_left (sum_normSq_mul_left_le _ _) ?_
      positivity
    _ = (‖A‖ * ‖B‖) ^ 2 *
        ∑ i : Y, ∑ j : Y, Complex.normSq (rowMat x i j) := by
      rw [← Matrix.star_eq_conjTranspose, norm_star]
      ring

omit [Fintype Y] [DecidableEq Y] in
/-- Differences of conjugations linearize through the mixed kernel. -/
theorem conjDouble_sub_eq (U V : Matrix Y Y ℂ) :
    conjDouble U - conjDouble V =
      conjMixed (U - V) U + conjMixed V (U - V) := by
  ext p q
  simp only [conjDouble_apply, conjMixed_apply, Matrix.sub_apply,
    Matrix.add_apply, map_sub]
  ring

/-- The conjugate double is `2`-Lipschitz on the unitary group, independently
of the matrix dimension.  This is the finite-dimensional estimate

`U X Uᴴ - V X Vᴴ = (U-V) X Uᴴ + V X (Uᴴ-Vᴴ)`

on the Hilbert--Schmidt space. -/
theorem l2_opNorm_conjDouble_sub_le_two {U V : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ)
    (hV : V ∈ Matrix.unitaryGroup Y ℂ) :
    ‖conjDouble U - conjDouble V‖ ≤ 2 * ‖U - V‖ := by
  cases isEmpty_or_nonempty Y with
  | inl hempty =>
    have hzero : conjDouble U - conjDouble V = 0 := by
      ext p q
      exact (hempty.false p.1).elim
    rw [hzero, norm_zero]
    positivity
  | inr hne =>
    have hUnorm : ‖U‖ = 1 := CStarRing.norm_of_mem_unitary hU
    have hVnorm : ‖V‖ = 1 := CStarRing.norm_of_mem_unitary hV
    calc
      ‖conjDouble U - conjDouble V‖ =
          ‖conjMixed (U - V) U + conjMixed V (U - V)‖ := by
        rw [conjDouble_sub_eq]
      _ ≤ ‖conjMixed (U - V) U‖ + ‖conjMixed V (U - V)‖ :=
        norm_add_le _ _
      _ ≤ ‖U - V‖ * ‖U‖ + ‖V‖ * ‖U - V‖ :=
        add_le_add (l2_opNorm_conjMixed_le _ _) (l2_opNorm_conjMixed_le _ _)
      _ = 2 * ‖U - V‖ := by rw [hUnorm, hVnorm]; ring

/-- Multiplicative defects at most double under the conjugate double. -/
theorem l2_opNorm_conjDouble_defect_le {W U V : Matrix Y Y ℂ}
    (hW : W ∈ Matrix.unitaryGroup Y ℂ) (hU : U ∈ Matrix.unitaryGroup Y ℂ)
    (hV : V ∈ Matrix.unitaryGroup Y ℂ) {ε : ℝ} (h : ‖W - U * V‖ ≤ ε) :
    ‖conjDouble W - conjDouble U * conjDouble V‖ ≤ 2 * ε := by
  rw [← conjDouble_mul]
  calc
    ‖conjDouble W - conjDouble (U * V)‖ ≤ 2 * ‖W - U * V‖ :=
      l2_opNorm_conjDouble_sub_le_two hW (mul_mem hU hV)
    _ ≤ 2 * ε := by linarith

namespace OpAlmostRepresentation

variable {G : Type u} [Group G]

/-- The adjoint almost-representation on the Hilbert space of matrices.

The model indexed by `Y` becomes the model indexed by `Y × Y`; the map is
`U ↦ U ⊗ Ū`.  Exact multiplicativity of `conjDouble` and its
dimension-free `2`-Lipschitz estimate transfer operator-norm defects without
any dimension loss. -/
def adjoint (A : OpAlmostRepresentation G) : OpAlmostRepresentation G where
  model n := doubleModel (A.model n)
  modelNonempty n := by
    rw [card_doubleModel]
    exact mul_pos (A.modelNonempty n) (A.modelNonempty n)
  map n g := ⟨conjDouble (A.map n g),
    conjDouble_mem_unitaryGroup (A.map n g).2⟩
  asymptoticallyMultiplicative g h ε hε := by
    obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative g h (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hd := l2_opNorm_conjDouble_defect_le (A.map n (g * h)).2
      (A.map n g).2 (A.map n h).2 (hN n hn)
    have htwo : (2 : ℝ) * (ε / 2) = ε := by ring
    rw [htwo] at hd
    exact hd

@[simp] theorem adjoint_model (A : OpAlmostRepresentation G) (n : ℕ) :
    (A.adjoint.model n : Type) =
      Prod (A.model n : Type) (A.model n : Type) := rfl

@[simp] theorem adjoint_map (A : OpAlmostRepresentation G) (n : ℕ) (g : G) :
    ((A.adjoint.map n g : Matrix (A.adjoint.model n) (A.adjoint.model n) ℂ)) =
      conjDouble (A.map n g) := rfl

end OpAlmostRepresentation

end GroupApproximation
