import GroupApproximation.Analysis.MFStablyFinite
import GroupApproximation.Analysis.StablyFiniteAmplification

/-!
# Matrices over a norm-matrix corona are Dedekind finite

Proof-ledger row `RE.01`, "every MF algebra is stably finite".
`Analysis/MFStablyFinite.lean` proves the `k = 1` half outright and reduces the
rest to one named statement, which it phrases as an isomorphism

> `M_I(Q_X)` is again a norm-matrix corona — concretely
> `CStarMatrix I I (NormMatrixCStarCorona X) ≃⋆ NormMatrixCStarCorona (I × X)`.

**That isomorphism is not what the reduction needs, and building it is not the
cheapest route.**  What `mul_star_eq_of_corner_isometry` consumes is a single
sentence about the target: *every one-sided inverse in it is two-sided*.  For
`Q_X` itself that is KT.06, `normMatrixCStarCorona_isDedekindFiniteMonoid`,
proved by lifting to coordinates, correcting there with the Neumann series, and
pushing back through the quotient.  The same three steps work one level up
without any isomorphism, because the coordinates of `M_I(Q_X)` are the
*amplified* finite matrices `M_{I × X n}`, and the coordinate correction
`UltraproductDedekindFinite.norm_swap_sub_one_le` is already stated at an
arbitrary finite index type.

So this file does not construct `M_I(ℓ∞)/M_I(c₀) ≃ ℓ∞/c₀` at all.  It assembles
a matrix of lifts into one amplified matrix sequence, runs KT.06's coordinate
estimate there, and reads the conclusion back off the blocks.  The two
comparisons that make "blockwise" and "whole" interchangeable are exactly the
ones `Analysis/StablyFiniteAmplification.lean` proves — a block is no larger
than the matrix, and the matrix is no larger than the sum of its blocks — and
they are restated here over an arbitrary finite index rather than `Fin m`,
since the reduction quantifies over an arbitrary `I`.

## What is proved

`mul_eq_one_symm_matrixCorona`: in `Matrix I I (NormMatrixCStarCorona X)`,
`x y = 1` implies `y x = 1`.

Nonemptiness of `I` is a hypothesis rather than a case split: it is what makes
the amplified coordinate space nonempty, which is what the finite-dimensional
correction asks for.  A consumer with an empty index has a subsingleton and
needs no theorem.
-/

namespace GroupApproximation
namespace MatrixCoronaFinite

open Filter Matrix KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

universe u

/-! ## Blocks over an arbitrary finite index

`Analysis/StablyFiniteAmplification.lean` proves these four statements for the
index `Fin m × Y` of `ampModel`.  The reduction quantifies over an arbitrary
finite `I`, so they are restated here at `I × Y`; the proofs are that file's,
with `Fin m` replaced by `I`.  Binders are per-declaration rather than section
variables, so that the two purely definitional lemmas carry no instances they
do not use. -/

section Blocks

/-- The `(i, j)` block of a matrix over a product index type. -/
def block {I Y : Type} (i j : I) (A : Matrix (I × Y) (I × Y) ℂ) :
    Matrix Y Y ℂ :=
  A.submatrix (fun y : Y ↦ ((i, y) : I × Y)) (fun y : Y ↦ ((j, y) : I × Y))

@[simp] theorem block_apply {I Y : Type} (i j : I)
    (A : Matrix (I × Y) (I × Y) ℂ) (x y : Y) :
    block i j A x y = A (i, x) (j, y) := rfl

/-- The pattern carrying the `(i, j)` block of `A` and nothing else. -/
def singleBlock {I Y : Type} [DecidableEq I] (i j : I)
    (A : Matrix (I × Y) (I × Y) ℂ) : Matrix (I × Y) (I × Y) ℂ :=
  Matrix.of fun p q ↦ if p.1 = i ∧ q.1 = j then A p q else 0

@[simp] theorem singleBlock_apply {I Y : Type} [DecidableEq I] (i j : I)
    (A : Matrix (I × Y) (I × Y) ℂ) (p q : I × Y) :
    singleBlock i j A p q = if p.1 = i ∧ q.1 = j then A p q else 0 := rfl

/-- **Block bound.**  Feeding the matrix a vector supported in the `j`-th
coordinate block and reading the `i`-th coordinate block of the answer computes
the `(i, j)` block exactly, so that block is no larger than the whole. -/
theorem norm_block_le {I Y : Type} [Fintype I] [DecidableEq I] [Fintype Y]
    [DecidableEq Y] (i j : I) (A : Matrix (I × Y) (I × Y) ℂ) :
    ‖block i j A‖ ≤ ‖A‖ := by
  classical
  refine l2_opNorm_le_of_sum_normSq_general _ (norm_nonneg A) fun v ↦ ?_
  set w : I × Y → ℂ := fun p ↦ if p.1 = j then v p.2 else 0 with hw
  have hval : ∀ y : Y, (block i j A *ᵥ v) y = (A *ᵥ w) (i, y) := by
    intro y
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
      Fintype.sum_prod_type]
    rw [Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl fun z _ ↦ ?_
      rw [hw]
      simp
    · intro l _ hl
      refine Finset.sum_eq_zero fun z _ ↦ ?_
      rw [hw]
      simp [hl]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  have hle : ∑ y : Y, Complex.normSq ((block i j A *ᵥ v) y)
      ≤ ∑ p : I × Y, Complex.normSq ((A *ᵥ w) p) := by
    rw [Fintype.sum_prod_type]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun y _ ↦ by rw [hval y]))
      ?_
    refine Finset.single_le_sum (f := fun l : I ↦
      ∑ y : Y, Complex.normSq ((A *ᵥ w) (l, y))) ?_ (Finset.mem_univ i)
    intro l _
    exact Finset.sum_nonneg fun y _ ↦ Complex.normSq_nonneg _
  refine le_trans hle (le_trans (sum_normSq_mulVec_le_general A w) ?_)
  have hwsum : ∑ p : I × Y, Complex.normSq (w p)
      = ∑ y : Y, Complex.normSq (v y) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [hw]
      simp
    · intro l _ hl
      refine Finset.sum_eq_zero fun y _ ↦ ?_
      rw [hw]
      simp [hl]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  rw [hwsum]

/-- **Single-block bound.**  The pattern carrying only the `(i, j)` block reads
the `j`-th coordinate block of the input, applies the block, and writes the
answer into the `i`-th coordinate block. -/
theorem norm_singleBlock_le {I Y : Type} [Fintype I] [DecidableEq I]
    [Fintype Y] [DecidableEq Y] (i j : I) (A : Matrix (I × Y) (I × Y) ℂ) :
    ‖singleBlock i j A‖ ≤ ‖block i j A‖ := by
  classical
  refine l2_opNorm_le_of_sum_normSq_general _ (norm_nonneg _) fun v ↦ ?_
  have hval_row : ∀ y : Y,
      (singleBlock i j A *ᵥ v) (i, y)
        = (block i j A *ᵥ fun z ↦ v (j, z)) y := by
    intro y
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.mulVec,
      dotProduct, Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl fun z _ ↦ ?_
      simp
    · intro l' _ hl'
      refine Finset.sum_eq_zero fun z _ ↦ ?_
      simp [hl']
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  have hval_off : ∀ l : I, l ≠ i → ∀ y : Y,
      (singleBlock i j A *ᵥ v) (l, y) = 0 := by
    intro l hl y
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun l' _ ↦ ?_
    refine Finset.sum_eq_zero fun z _ ↦ ?_
    simp [hl]
  have hsum : ∑ p : I × Y, Complex.normSq ((singleBlock i j A *ᵥ v) p)
      = ∑ y : Y, Complex.normSq ((block i j A *ᵥ fun z ↦ v (j, z)) y) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [hval_row y]
    · intro l _ hl
      refine Finset.sum_eq_zero fun y _ ↦ ?_
      rw [hval_off l hl y]
      simp
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  rw [hsum]
  refine le_trans (sum_normSq_mulVec_le_general (block i j A) _) ?_
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [Fintype.sum_prod_type]
  refine Finset.single_le_sum (f := fun l : I ↦
    ∑ y : Y, Complex.normSq (v (l, y))) ?_ (Finset.mem_univ j)
  intro l _
  exact Finset.sum_nonneg fun y _ ↦ Complex.normSq_nonneg _

/-- A matrix over a product index type is the sum of its single-block
patterns. -/
theorem sum_singleBlock {I Y : Type} [Fintype I] [DecidableEq I]
    (A : Matrix (I × Y) (I × Y) ℂ) :
    ∑ i : I, ∑ j : I, singleBlock i j A = A := by
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
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    simp [Ne.symm hi]
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

/-- **The whole is no larger than the sum of the blocks.** -/
theorem norm_le_sum_blocks {I Y : Type} [Fintype I] [DecidableEq I] [Fintype Y]
    [DecidableEq Y] (A : Matrix (I × Y) (I × Y) ℂ) :
    ‖A‖ ≤ ∑ i : I, ∑ j : I, ‖block i j A‖ := by
  calc ‖A‖ = ‖∑ i : I, ∑ j : I, singleBlock i j A‖ := by
        rw [sum_singleBlock]
    _ ≤ ∑ i : I, ‖∑ j : I, singleBlock i j A‖ := norm_sum_le _ _
    _ ≤ ∑ i : I, ∑ j : I, ‖singleBlock i j A‖ :=
        Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _
    _ ≤ ∑ i : I, ∑ j : I, ‖block i j A‖ :=
        Finset.sum_le_sum fun i _ ↦
          Finset.sum_le_sum fun j _ ↦ norm_singleBlock_le i j A

end Blocks

/-! ## Assembling a matrix of lifts -/

section Assemble

/-- The numerator's multiplication is coordinatewise. -/
theorem coord_mul (X : ℕ → FiniteModel)
    (x y : BoundedMatrixSequence (fun n ↦ X n)) (n : ℕ) :
    (x * y) n = x n * y n := rfl

/-- Evaluating a finite sum of bounded sequences at a coordinate is the sum of
the evaluations: the algebra of the numerator is coordinatewise. -/
theorem coord_sum {I : Type} [DecidableEq I] (X : ℕ → FiniteModel)
    (f : I → BoundedMatrixSequence (fun n ↦ X n)) (s : Finset I) (n : ℕ) :
    (∑ k ∈ s, f k) n = ∑ k ∈ s, (f k) n := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk]
      show (f k) n + ((∑ m ∈ s, f m) n) = (f k) n + ∑ m ∈ s, (f m) n
      rw [ih]

/-- The amplified coordinate matrix of a matrix of bounded sequences: its
`(i, j)` block at coordinate `n` is the `n`-th coordinate of the `(i, j)`
entry. -/
noncomputable def assemble {I : Type} (X : ℕ → FiniteModel)
    (a : I → I → BoundedMatrixSequence (fun n ↦ X n)) (n : ℕ) :
    Matrix (I × X n) (I × X n) ℂ :=
  Matrix.of fun p q ↦ (a p.1 q.1) n p.2 q.2

@[simp] theorem block_assemble {I : Type} (X : ℕ → FiniteModel)
    (a : I → I → BoundedMatrixSequence (fun n ↦ X n)) (i j : I) (n : ℕ) :
    block i j (assemble X a n) = (a i j) n := rfl

theorem norm_assemble_le {I : Type} [Fintype I] [DecidableEq I]
    (X : ℕ → FiniteModel)
    (a : I → I → BoundedMatrixSequence (fun n ↦ X n)) (n : ℕ) :
    ‖assemble X a n‖ ≤ ∑ i : I, ∑ j : I, ‖a i j‖ := by
  refine le_trans (norm_le_sum_blocks (assemble X a n)) ?_
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
  rw [block_assemble]
  exact boundedMatrixSequence_coord_norm_le (fun n ↦ X n) (a i j) n

theorem assemble_mul {I : Type} [Fintype I] [DecidableEq I]
    (X : ℕ → FiniteModel)
    (a b : I → I → BoundedMatrixSequence (fun n ↦ X n)) (n : ℕ) :
    assemble X a n * assemble X b n
      = assemble X (fun i j ↦ ∑ k : I, a i k * b k j) n := by
  classical
  ext p q
  show ∑ r : I × X n, (a p.1 r.1) n p.2 r.2 * (b r.1 q.1) n r.2 q.2
    = ((∑ k : I, a p.1 k * b k q.1) n) p.2 q.2
  rw [coord_sum, Matrix.sum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  show ∑ z : X n, (a p.1 k) n p.2 z * (b k q.1) n z q.2
    = ((a p.1 k) n * (b k q.1) n) p.2 q.2
  rw [Matrix.mul_apply]

theorem assemble_one {I : Type} [DecidableEq I] (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (n : ℕ) :
    assemble X (fun i j : I ↦ if i = j then (1 : BoundedMatrixSequence
      (fun n ↦ X n)) else 0) n = 1 := by
  classical
  ext p q
  show (if p.1 = q.1 then (1 : BoundedMatrixSequence (fun n ↦ X n)) else 0) n
      p.2 q.2 = (1 : Matrix (I × X n) (I × X n) ℂ) p q
  by_cases h : p.1 = q.1
  · rw [if_pos h]
    show (1 : Matrix (X n) (X n) ℂ) p.2 q.2 = _
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases h2 : p.2 = q.2
    · rw [if_pos h2, if_pos (Prod.ext h h2)]
    · rw [if_neg h2, if_neg (fun hc ↦ h2 (congrArg Prod.snd hc))]
  · rw [if_neg h]
    show (0 : Matrix (X n) (X n) ℂ) p.2 q.2 = _
    rw [Matrix.zero_apply, Matrix.one_apply,
      if_neg (fun hc ↦ h (congrArg Prod.fst hc))]

end Assemble

/-! ## The amplified corona is Dedekind finite -/

section Corona

/-- The blockwise reading of the multiplicative defect of two assembled
sequences. -/
theorem block_assemble_mul_sub_one {I : Type} [Fintype I] [DecidableEq I]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (a b : I → I → BoundedMatrixSequence (fun n ↦ X n)) (i j : I) (n : ℕ) :
    block i j (assemble X a n * assemble X b n - 1)
      = ((∑ k : I, a i k * b k j) -
          (if i = j then (1 : BoundedMatrixSequence (fun n ↦ X n))
            else 0)) n := by
  have h1 : block i j (assemble X a n * assemble X b n)
      = (∑ k : I, a i k * b k j) n := by
    rw [assemble_mul, block_assemble]
  have h2 : block i j (1 : Matrix (I × X n) (I × X n) ℂ)
      = (if i = j then (1 : BoundedMatrixSequence (fun n ↦ X n))
          else 0) n := by
    rw [← assemble_one (I := I) X n, block_assemble]
  have h3 : block i j (assemble X a n * assemble X b n - 1)
      = block i j (assemble X a n * assemble X b n)
        - block i j (1 : Matrix (I × X n) (I × X n) ℂ) := by
    ext p q
    simp [block]
  rw [h3, h1, h2]
  rfl

/-- The corona class of an entry of a matrix product of lifts. -/
theorem mk_sum_mul {I : Type} [Fintype I] (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)]
    {a b : I → I → BoundedMatrixSequence (fun n ↦ X n)}
    {x y : Matrix I I (NormMatrixCStarCorona (fun n ↦ X n))}
    (ha : ∀ i j, normMatrixCStarCoronaMk (fun n ↦ X n) (a i j) = x i j)
    (hb : ∀ i j, normMatrixCStarCoronaMk (fun n ↦ X n) (b i j) = y i j)
    (i j : I) :
    normMatrixCStarCoronaMk (fun n ↦ X n) (∑ k : I, a i k * b k j)
      = (x * y) i j := by
  rw [map_sum, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [map_mul, ha, hb]

/-- The corona class of an entry of the identity. -/
theorem mk_one_entry {I : Type} [DecidableEq I] (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (i j : I) :
    normMatrixCStarCoronaMk (fun n ↦ X n)
        (if i = j then (1 : BoundedMatrixSequence (fun n ↦ X n)) else 0)
      = (1 : Matrix I I (NormMatrixCStarCorona (fun n ↦ X n))) i j := by
  rw [Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h, map_one]
  · rw [if_neg h, if_neg h, map_zero]

/-- **One-sided inverses in `M_I(Q_X)` are two-sided.**

The coordinates of a matrix over `Q_X` are the amplified finite matrices
`M_{I × X n}`; KT.06's Neumann correction
`UltraproductDedekindFinite.norm_swap_sub_one_le` applies there verbatim, and
the two block comparisons carry the hypothesis down to the coordinates and the
conclusion back up. -/
theorem mul_eq_one_symm_matrixCorona {I : Type} [Fintype I] [DecidableEq I]
    [Nonempty I] (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    {x y : Matrix I I (NormMatrixCStarCorona (fun n ↦ X n))} (hxy : x * y = 1) :
    y * x = 1 := by
  classical
  have hsurj := normMatrixCStarCoronaMk_surjective (fun n ↦ X n)
  set a : I → I → BoundedMatrixSequence (fun n ↦ X n) :=
    fun i j ↦ Function.surjInv hsurj (x i j) with hadef
  set b : I → I → BoundedMatrixSequence (fun n ↦ X n) :=
    fun i j ↦ Function.surjInv hsurj (y i j) with hbdef
  have ha : ∀ i j, normMatrixCStarCoronaMk (fun n ↦ X n) (a i j) = x i j :=
    fun i j ↦ Function.surjInv_eq hsurj (x i j)
  have hb : ∀ i j, normMatrixCStarCoronaMk (fun n ↦ X n) (b i j) = y i j :=
    fun i j ↦ Function.surjInv_eq hsurj (y i j)
  -- the blockwise defect of `A B - 1` is null, hence so is the whole
  have hblock : ∀ i j : I, Tendsto
      (fun n ↦ ‖block i j (assemble X a n * assemble X b n - 1)‖) cofinite
      (nhds 0) := by
    intro i j
    have hzero : normMatrixCStarCoronaMk (fun n ↦ X n)
        ((∑ k : I, a i k * b k j) -
          (if i = j then (1 : BoundedMatrixSequence (fun n ↦ X n)) else 0))
        = 0 := by
      rw [map_sub, mk_sum_mul X ha hb i j, mk_one_entry X i j, hxy, sub_self]
    have hnull := (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) _).mp hzero
    exact hnull.congr fun n ↦ by rw [block_assemble_mul_sub_one]
  have hAB : Tendsto (fun n ↦ ‖assemble X a n * assemble X b n - 1‖) cofinite
      (nhds 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _)
      (Eventually.of_forall fun n ↦
        norm_le_sum_blocks (assemble X a n * assemble X b n - 1)) ?_
    have hsum : Tendsto
        (fun n ↦ ∑ i : I, ∑ j : I,
          ‖block i j (assemble X a n * assemble X b n - 1)‖) cofinite
        (nhds (∑ _i : I, ∑ _j : I, (0 : ℝ))) :=
      tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦ hblock i j
    simpa using hsum
  -- the coordinate correction
  have hMa0 : (0 : ℝ) ≤ ∑ i : I, ∑ j : I, ‖a i j‖ :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ norm_nonneg _
  have hhalf : ∀ᶠ n in (cofinite : Filter ℕ),
      ‖assemble X a n * assemble X b n - 1‖ ≤ (1 / 2 : ℝ) := by
    have hnear := (Metric.tendsto_nhds.mp hAB) (1 / 2 : ℝ) (by norm_num)
    filter_upwards [hnear] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  have hBA : Tendsto (fun n ↦ ‖assemble X b n * assemble X a n - 1‖) cofinite
      (nhds 0) := by
    refine squeeze_zero'
      (g := fun n ↦ 2 * ((∑ i : I, ∑ j : I, ‖a i j‖) *
        (∑ i : I, ∑ j : I, ‖b i j‖)) *
        ‖assemble X a n * assemble X b n - 1‖)
      (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ ?_
    · filter_upwards [hhalf] with n hn
      refine le_trans
        (norm_swap_sub_one_le (Y := I × X n) inferInstance
          (assemble X a n) (assemble X b n) hn) ?_
      have h1 : ‖assemble X a n‖ * ‖assemble X b n‖ ≤
          (∑ i : I, ∑ j : I, ‖a i j‖) * (∑ i : I, ∑ j : I, ‖b i j‖) :=
        mul_le_mul (norm_assemble_le X a n) (norm_assemble_le X b n)
          (norm_nonneg _) hMa0
      nlinarith [norm_nonneg (assemble X a n), norm_nonneg (assemble X b n),
        norm_nonneg (assemble X a n * assemble X b n - 1)]
    · have hc := hAB.const_mul
        (2 * ((∑ i : I, ∑ j : I, ‖a i j‖) * (∑ i : I, ∑ j : I, ‖b i j‖)))
      simpa using hc
  -- read the conclusion off the blocks
  ext i j
  have hnull : Tendsto (fun n ↦
      ‖((∑ k : I, b i k * a k j) -
        (if i = j then (1 : BoundedMatrixSequence (fun n ↦ X n)) else 0)) n‖)
      cofinite (nhds 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _)
      (Eventually.of_forall fun n ↦ ?_) hBA
    rw [← block_assemble_mul_sub_one X b a i j n]
    exact norm_block_le i j (assemble X b n * assemble X a n - 1)
  have hmk : normMatrixCStarCoronaMk (fun n ↦ X n)
      ((∑ k : I, b i k * a k j) -
        (if i = j then (1 : BoundedMatrixSequence (fun n ↦ X n)) else 0)) = 0 :=
    (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) _).mpr hnull
  rw [map_sub, sub_eq_zero, mk_sum_mul X hb ha i j, mk_one_entry X i j] at hmk
  exact hmk

end Corona

/-! ## Every MF algebra is stably finite -/

section StablyFinite

/-- **Every MF algebra is stably finite**, which is the printed sentence of
`p:D-preamble` taken whole.

The `k = 1` case is `MFStablyFinite.mul_star_eq_one_of_hasMFEmbedding`, and this
is that argument with the amplification in place of the algebra: the embedding
`e` is applied entrywise, which is a non-unital `⋆`-homomorphism of matrix
algebras, so `E 1` is a projection of `M_I(Q_X)` and the manuscript's
`σ = v + (1 - E 1)` computation runs in its corner.  The one input the corner
computation needs about the target -- that every isometry there is a unitary --
is `mul_eq_one_symm_matrixCorona` above.

Nothing is assumed about `I` beyond finiteness: the empty index gives a
subsingleton, where the conclusion holds for want of an entry to check. -/
theorem cstarMatrix_mul_star_eq_one_of_hasMFEmbedding
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (hA : HasMFEmbedding A) (I : Type) [Fintype I] [DecidableEq I]
    {v : CStarMatrix I I A} (hv : star v * v = 1) : v * star v = 1 := by
  classical
  rcases isEmpty_or_nonempty I with hI | hI
  · ext i j
    exact hI.elim i
  · rcases hA with ⟨X, hne, _hX, _hmono, e, he⟩
    letI : ∀ n, Nonempty (X n) := hne
    set E : CStarMatrix I I A →⋆ₙₐ[ℂ]
        CStarMatrix I I (NormMatrixCStarCorona (fun n ↦ X n)) :=
      CStarMatrix.mapₙₐ e with hEdef
    have hEapply : ∀ (M : CStarMatrix I I A) (i j : I), E M i j = e (M i j) :=
      fun _ _ _ ↦ rfl
    have hEinj : Function.Injective E := by
      intro M N h
      ext i j
      have hij : E M i j = E N i j := by rw [h]
      rw [hEapply, hEapply] at hij
      exact he hij
    have hfinite : ∀ z : CStarMatrix I I (NormMatrixCStarCorona (fun n ↦ X n)),
        star z * z = 1 → z * star z = 1 := fun z hz ↦
      mul_eq_one_symm_matrixCorona X hz
    have hPidem : E 1 * E 1 = E 1 := by
      rw [← map_mul, one_mul]
    have hPsa : star (E 1) = E 1 := by
      rw [← map_star, star_one]
    have hP : IsStarProjection (E 1) := ⟨hPidem, hPsa⟩
    have hPv : E 1 * E v = E v := by
      rw [← map_mul, one_mul]
    have hvP : E v * E 1 = E v := by
      rw [← map_mul, mul_one]
    have hstarv : star (E v) = E (star v) := (map_star E v).symm
    have hev : star (E v) * E v = E 1 := by
      rw [hstarv, ← map_mul, hv]
    have hmain : E v * star (E v) = E 1 :=
      mul_star_eq_of_corner_isometry hfinite hP hPv hvP hev
    have hcomp : E (v * star v) = E v * star (E v) := by
      rw [map_mul, hstarv]
    exact hEinj (hcomp.trans hmain)

/-- The same statement in the manuscript's `k ≥ 1` indexing: for an MF algebra
`A` and every `k`, every isometry of `M_k(A)` is a unitary. -/
theorem fin_mul_star_eq_one_of_hasMFEmbedding
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (hA : HasMFEmbedding A) (k : ℕ)
    {v : CStarMatrix (Fin k) (Fin k) A} (hv : star v * v = 1) :
    v * star v = 1 :=
  cstarMatrix_mul_star_eq_one_of_hasMFEmbedding hA (Fin k) hv

/-- **`p:D-preamble`'s opening sentence, as a closed proposition.**  Every MF
algebra is stably finite, with stable finiteness in the shape
`lem:faithfultrace`(2) states it. -/
def MFAlgebraIsStablyFinite : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A],
    HasMFEmbedding A →
      ∀ (I : Type) [Fintype I] [DecidableEq I]
        (v : CStarMatrix I I A), star v * v = 1 → v * star v = 1

/-- **Every MF algebra is stably finite.** -/
theorem mfAlgebra_isStablyFinite : MFAlgebraIsStablyFinite.{u} := by
  intro A _ _ _ hA I _ _ v hv
  exact cstarMatrix_mul_star_eq_one_of_hasMFEmbedding hA I hv

end StablyFinite

end MatrixCoronaFinite
end GroupApproximation
