import GroupApproximation.Sofic.AmplifiedBlockNorms

/-!
# Blocks of an amplified matrix, and what they buy for `RE.01`

`non_mf_groups_exist.tex` opens *A stably finite non-MF group algebra* with
"Every MF algebra is stably finite \cite{BK}", which is proof-ledger row
`RE.01`.  `Analysis/MFStablyFinite.lean` proves the `k = 1` half outright and
reduces the rest to one named statement:

> `M_I(Q_X)` is again a norm-matrix corona — concretely
> `CStarMatrix I I (NormMatrixCStarCorona X) ≃⋆ NormMatrixCStarCorona (I × X)`.

and records that this needs the operator norm of an amplified matrix to be
comparable, in both directions, with the operator norms of its blocks.  That
module's docstring says both directions are missing from mathlib *and from this
repository*.  **The second half of that is wrong**, and this file is the
correction.

## What is proved

For matrices over the amplified index type `Fin m × Y` of
`Sofic/AmplifiedBlockNorms.lean`:

* `norm_block_le` — every block, diagonal or not, is no larger than the whole
  matrix.  `AmplifiedBlocks.l2_opNorm_block_le` proves this for the diagonal
  blocks; the proof here is that one with the column block released from the
  row block, which is the version an off-diagonal entry of a matrix over a
  corona needs.
* `norm_singleBlock_le` — the pattern with one block of `A` in position
  `(i, j)` and zeros elsewhere is no larger than that block.
* `sum_singleBlock` — a matrix is the sum of its `m²` single-block patterns.
* `norm_le_sum_blocks` — hence the whole is no larger than the sum of the
  norms of its blocks.

Together these are exactly the two comparisons the amplification needs, and
the two corollaries state them in the form the corona consumes:

* `tendsto_norm_block` — the blocks of a null sequence are null;
* `tendsto_norm_of_forall_block` — a sequence all of whose blocks are null is
  null.

The second is why the *sum* bound is needed rather than a maximum: nullity of
finitely many block sequences has to imply nullity of the assembled one, and
`m²` is a constant.

## What remains for `RE.01`, precisely

Nothing analytic.  What is left is bookkeeping, and it is worth writing down so
that the row is not mistaken for an open problem:

1. a choice of lift `NormMatrixCStarCorona X → BoundedMatrixSequence X` right
   inverse to the quotient map (`normMatrixCStarCoronaMk_surjective`);
2. the assembly `(Fin k → Fin k → BoundedMatrixSequence X) →
   BoundedMatrixSequence (fun n ↦ ampModel k (X n))`, whose `Memℓp` obligation
   is `norm_le_sum_blocks`;
3. the six homomorphism laws for `mk ∘ assemble ∘ (lift ∘ e)`, each of which
   reduces to `tendsto_norm_of_forall_block` applied to the blockwise
   difference, since `e` satisfies the law and `mk ∘ lift = id`;
4. injectivity, which is `tendsto_norm_block` plus injectivity of `e`;
5. the model data: `card (ampModel k (X n)) = k * card (X n)` is strictly
   monotone for `k ≥ 1`, and `k = 0` is a subsingleton.

None of this is in place, so `RE.01` is **not** closed by this file, and
`MFStablyFinite.mul_star_eq_one_of_matrixHasMFEmbedding` still consumes its
amplification hypothesis.  What changes is the size of the debt: it is five
mechanical steps rather than a missing C-star theorem.
-/

namespace GroupApproximation
namespace StablyFiniteAmplification

open Matrix KazhdanCornerMatrices AmplifiedBlocks
open scoped Matrix.Norms.L2Operator

variable {m : ℕ} {Y : FiniteModel}

/-! ## Blocks -/

/-- The `(i, j)` block of a matrix over the amplified index type. -/
def block (i j : Fin m) (A : Matrix (ampModel m Y) (ampModel m Y) ℂ) :
    Matrix Y Y ℂ :=
  A.submatrix (fun y : Y.carrier => ((i, y) : Fin m × Y.carrier))
    (fun y : Y.carrier => ((j, y) : Fin m × Y.carrier))

@[simp] theorem block_apply (i j : Fin m)
    (A : Matrix (ampModel m Y) (ampModel m Y) ℂ) (x y : Y.carrier) :
    block i j A x y = A (i, x) (j, y) := rfl

/-- The pattern carrying the `(i, j)` block of `A` and nothing else. -/
def singleBlock (i j : Fin m) (A : Matrix (ampModel m Y) (ampModel m Y) ℂ) :
    Matrix (ampModel m Y) (ampModel m Y) ℂ :=
  Matrix.of fun p q => if p.1 = i ∧ q.1 = j then A p q else 0

@[simp] theorem singleBlock_apply (i j : Fin m)
    (A : Matrix (ampModel m Y) (ampModel m Y) ℂ)
    (p q : Fin m × Y.carrier) :
    singleBlock i j A p q = if p.1 = i ∧ q.1 = j then A p q else 0 := rfl

/-! ## A block is no larger than the matrix -/

/-- **Block bound, off the diagonal too.**  Feeding the matrix a vector
supported in the `j`-th coordinate block and reading the `i`-th coordinate
block of the answer computes the `(i, j)` block exactly, so that block's norm
is bounded by the whole matrix's. -/
theorem norm_block_le (i j : Fin m)
    (A : Matrix (ampModel m Y) (ampModel m Y) ℂ) : ‖block i j A‖ ≤ ‖A‖ := by
  classical
  refine l2_opNorm_le_of_sum_normSq_general _ (norm_nonneg A) fun v => ?_
  set w : Fin m × Y.carrier → ℂ :=
    fun p => if p.1 = j then v p.2 else 0 with hw
  have hval : ∀ y : Y.carrier,
      (block i j A *ᵥ v) y = (A *ᵥ w) (i, y) := by
    intro y
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
      Fintype.sum_prod_type]
    rw [Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl fun z _ => ?_
      rw [hw]
      simp
    · intro l _ hl
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [hw]
      simp [hl]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  have hle : ∑ y : Y.carrier, Complex.normSq ((block i j A *ᵥ v) y)
      ≤ ∑ p : Fin m × Y.carrier, Complex.normSq ((A *ᵥ w) p) := by
    rw [Fintype.sum_prod_type]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun y _ => by rw [hval y]))
      ?_
    refine Finset.single_le_sum (f := fun l : Fin m =>
      ∑ y : Y.carrier, Complex.normSq ((A *ᵥ w) (l, y))) ?_ (Finset.mem_univ i)
    intro l _
    exact Finset.sum_nonneg fun y _ => Complex.normSq_nonneg _
  refine le_trans hle (le_trans (sum_normSq_mulVec_le_general A w) ?_)
  have hwsum : ∑ p : Fin m × Y.carrier, Complex.normSq (w p)
      = ∑ y : Y.carrier, Complex.normSq (v y) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [hw]
      simp
    · intro l _ hl
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [hw]
      simp [hl]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  rw [hwsum]

/-! ## A single-block pattern is no larger than its block -/

/-- **Single-block bound.**  The pattern carrying only the `(i, j)` block acts
by reading the `j`-th coordinate block of the input, applying the block, and
writing the answer into the `i`-th coordinate block; so it is no larger than
the block. -/
theorem norm_singleBlock_le (i j : Fin m)
    (A : Matrix (ampModel m Y) (ampModel m Y) ℂ) :
    ‖singleBlock i j A‖ ≤ ‖block i j A‖ := by
  classical
  refine l2_opNorm_le_of_sum_normSq_general _ (norm_nonneg _) fun v => ?_
  have hval_row : ∀ y : Y.carrier,
      (singleBlock i j A *ᵥ v) (i, y)
        = (block i j A *ᵥ fun z => v (j, z)) y := by
    intro y
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.mulVec,
      dotProduct, Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl fun z _ => ?_
      simp
    · intro l' _ hl'
      refine Finset.sum_eq_zero fun z _ => ?_
      simp [hl']
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  have hval_off : ∀ l : Fin m, l ≠ i → ∀ y : Y.carrier,
      (singleBlock i j A *ᵥ v) (l, y) = 0 := by
    intro l hl y
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun l' _ => ?_
    refine Finset.sum_eq_zero fun z _ => ?_
    simp [hl]
  have hsum : ∑ p : Fin m × Y.carrier,
        Complex.normSq ((singleBlock i j A *ᵥ v) p)
      = ∑ y : Y.carrier,
          Complex.normSq ((block i j A *ᵥ fun z => v (j, z)) y) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [hval_row y]
    · intro l _ hl
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [hval_off l hl y]
      simp
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  rw [hsum]
  refine le_trans (sum_normSq_mulVec_le_general (block i j A) _) ?_
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [Fintype.sum_prod_type]
  refine Finset.single_le_sum (f := fun l : Fin m =>
    ∑ y : Y.carrier, Complex.normSq (v (l, y))) ?_ (Finset.mem_univ j)
  intro l _
  exact Finset.sum_nonneg fun y _ => Complex.normSq_nonneg _

/-! ## The matrix is the sum of its blocks -/

/-- A matrix over the amplified index type is the sum of its `m²`
single-block patterns. -/
theorem sum_singleBlock (A : Matrix (ampModel m Y) (ampModel m Y) ℂ) :
    ∑ i : Fin m, ∑ j : Fin m, singleBlock i j A = A := by
  classical
  ext p q
  simp only [Matrix.sum_apply, singleBlock_apply]
  rw [Finset.sum_eq_single p.1]
  · rw [Finset.sum_eq_single q.1]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [Ne.symm hi]
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

/-- **The whole is no larger than the sum of the blocks.**  This is the
direction that makes blockwise nullity imply nullity, and the constant `m²` is
what makes it usable in a corona. -/
theorem norm_le_sum_blocks (A : Matrix (ampModel m Y) (ampModel m Y) ℂ) :
    ‖A‖ ≤ ∑ i : Fin m, ∑ j : Fin m, ‖block i j A‖ := by
  calc ‖A‖ = ‖∑ i : Fin m, ∑ j : Fin m, singleBlock i j A‖ := by
        rw [sum_singleBlock]
    _ ≤ ∑ i : Fin m, ‖∑ j : Fin m, singleBlock i j A‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin m, ∑ j : Fin m, ‖singleBlock i j A‖ :=
        Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i : Fin m, ∑ j : Fin m, ‖block i j A‖ :=
        Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => norm_singleBlock_le i j A

/-! ## The two statements the corona consumes -/

/-- **Blocks of a null sequence are null.**  This is what makes the assembled
homomorphism injective: a class that dies in the amplified corona dies in every
coordinate. -/
theorem tendsto_norm_block {l : Filter ℕ} {X : ℕ → FiniteModel}
    (a : ∀ n, Matrix (ampModel m (X n)) (ampModel m (X n)) ℂ)
    (h : Filter.Tendsto (fun n ↦ ‖a n‖) l (nhds 0)) (i j : Fin m) :
    Filter.Tendsto (fun n ↦ ‖block i j (a n)‖) l (nhds 0) :=
  squeeze_zero' (Filter.Eventually.of_forall fun n ↦ norm_nonneg (block i j (a n)))
    (Filter.Eventually.of_forall fun n ↦ norm_block_le i j (a n)) h

/-- **A sequence with null blocks is null.**  This is what makes the assembled
map well defined and multiplicative: the blockwise difference of two lifts is
null in each of `m²` coordinates, hence null. -/
theorem tendsto_norm_of_forall_block {l : Filter ℕ} {X : ℕ → FiniteModel}
    (a : ∀ n, Matrix (ampModel m (X n)) (ampModel m (X n)) ℂ)
    (h : ∀ i j : Fin m,
      Filter.Tendsto (fun n ↦ ‖block i j (a n)‖) l (nhds 0)) :
    Filter.Tendsto (fun n ↦ ‖a n‖) l (nhds 0) := by
  refine squeeze_zero' (Filter.Eventually.of_forall fun n ↦ norm_nonneg (a n))
    (Filter.Eventually.of_forall fun n ↦ norm_le_sum_blocks (a n)) ?_
  have hsum : Filter.Tendsto
      (fun n ↦ ∑ i : Fin m, ∑ j : Fin m, ‖block i j (a n)‖) l
      (nhds (∑ _i : Fin m, ∑ _j : Fin m, (0 : ℝ))) :=
    tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦ h i j
  simpa using hsum

end StablyFiniteAmplification
end GroupApproximation
