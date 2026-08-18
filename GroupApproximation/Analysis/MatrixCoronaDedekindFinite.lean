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
*amplified* finite matrices `M_{I × X n}` and the coordinate correction
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

* `mul_eq_one_symm_matrixCorona` — in `Matrix I I (NormMatrixCStarCorona X)`,
  `x y = 1` implies `y x = 1`.

The empty index type is not special-cased here: the argument needs a nonempty
coordinate space only to invoke the finite-dimensional correction, and the
consumers below supply it or dispatch the subsingleton case directly.
-/

namespace GroupApproximation
namespace MatrixCoronaFinite

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

/-! ## Blocks over an arbitrary finite index

`Analysis/StablyFiniteAmplification.lean` proves these four statements for the
index `Fin m × Y` of `ampModel`.  The reduction quantifies over an arbitrary
finite `I`, so they are restated here at `I × Y`; the proofs are that file's,
with `Fin m` replaced by `I`. -/

section Blocks

variable {I : Type} [Fintype I] [DecidableEq I]
variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-- The `(i, j)` block of a matrix over a product index type. -/
def block (i j : I) (A : Matrix (I × Y) (I × Y) ℂ) : Matrix Y Y ℂ :=
  A.submatrix (fun y : Y ↦ ((i, y) : I × Y)) (fun y : Y ↦ ((j, y) : I × Y))

@[simp] theorem block_apply (i j : I) (A : Matrix (I × Y) (I × Y) ℂ)
    (x y : Y) : block i j A x y = A (i, x) (j, y) := rfl

/-- The pattern carrying the `(i, j)` block of `A` and nothing else. -/
def singleBlock (i j : I) (A : Matrix (I × Y) (I × Y) ℂ) :
    Matrix (I × Y) (I × Y) ℂ :=
  Matrix.of fun p q ↦ if p.1 = i ∧ q.1 = j then A p q else 0

@[simp] theorem singleBlock_apply (i j : I) (A : Matrix (I × Y) (I × Y) ℂ)
    (p q : I × Y) :
    singleBlock i j A p q = if p.1 = i ∧ q.1 = j then A p q else 0 := rfl

/-- **Block bound.**  Feeding the matrix a vector supported in the `j`-th
coordinate block and reading the `i`-th coordinate block of the answer computes
the `(i, j)` block exactly. -/
theorem norm_block_le (i j : I) (A : Matrix (I × Y) (I × Y) ℂ) :
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

/-- **Single-block bound.** -/
theorem norm_singleBlock_le (i j : I) (A : Matrix (I × Y) (I × Y) ℂ) :
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
theorem sum_singleBlock (A : Matrix (I × Y) (I × Y) ℂ) :
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
theorem norm_le_sum_blocks (A : Matrix (I × Y) (I × Y) ℂ) :
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

variable {I : Type} [Fintype I] [DecidableEq I]
variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

/-- The amplified coordinate matrix of a matrix of bounded sequences: its
`(i, j)` block at coordinate `n` is the `n`-th coordinate of the `(i, j)`
entry. -/
noncomputable def assemble (a : I → I → BoundedMatrixSequence (fun n ↦ X n))
    (n : ℕ) : Matrix (I × X n) (I × X n) ℂ :=
  Matrix.of fun p q ↦ (a p.1 q.1) n p.2 q.2

@[simp] theorem block_assemble
    (a : I → I → BoundedMatrixSequence (fun n ↦ X n)) (i j : I) (n : ℕ) :
    block i j (assemble X a n) = (a i j) n := rfl

theorem norm_assemble_le (a : I → I → BoundedMatrixSequence (fun n ↦ X n))
    (n : ℕ) : ‖assemble X a n‖ ≤ ∑ i : I, ∑ j : I, ‖a i j‖ := by
  refine le_trans (norm_le_sum_blocks (assemble X a n)) ?_
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
  rw [block_assemble]
  exact boundedMatrixSequence_coord_norm_le (fun n ↦ X n) (a i j) n

theorem assemble_mul (a b : I → I → BoundedMatrixSequence (fun n ↦ X n))
    (n : ℕ) :
    assemble X a n * assemble X b n
      = assemble X (fun i j ↦ ∑ k : I, a i k * b k j) n := by
  classical
  ext p q
  show ∑ r : I × X n, (a p.1 r.1) n p.2 r.2 * (b r.1 q.1) n r.2 q.2
    = ((∑ k : I, a p.1 k * b k q.1) n) p.2 q.2
  rw [Fintype.sum_prod_type]
  have hcoord : ((∑ k : I, a p.1 k * b k q.1) n) p.2 q.2
      = ∑ k : I, ((a p.1 k) n * (b k q.1) n) p.2 q.2 := by
    classical
    induction (Finset.univ : Finset I) using Finset.induction_on with
    | empty => simp
    | insert k s hk ih => simp [Finset.sum_insert hk, ih]
  rw [hcoord]
  exact Finset.sum_congr rfl fun k _ ↦ (Matrix.mul_apply).symm ▸ rfl

theorem assemble_one (n : ℕ) :
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

variable {I : Type} [Fintype I] [DecidableEq I]
variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

/-- The blockwise reading of a matrix product of assembled sequences. -/
theorem block_assemble_mul_sub_one
    (a b : I → I → BoundedMatrixSequence (fun n ↦ X n)) (i j : I) (n : ℕ) :
    block i j (assemble X a n * assemble X b n - 1)
      = ((∑ k : I, a i k * b k j) -
          (if i = j then (1 : BoundedMatrixSequence (fun n ↦ X n))
            else 0)) n := by
  have h3 : block i j (assemble X a n * assemble X b n - 1)
      = block i j (assemble X a n * assemble X b n)
        - block i j (1 : Matrix (I × X n) (I × X n) ℂ) := by
    ext p q
    simp [block]
  rw [h3, assemble_mul, block_assemble, ← assemble_one (I := I) X n,
    block_assemble]
  rfl

/-- The corona class of a matrix product of lifts. -/
theorem mk_sum_mul
    {a b : I → I → BoundedMatrixSequence (fun n ↦ X n)}
    {x y : Matrix I I (NormMatrixCStarCorona (fun n ↦ X n))}
    (ha : ∀ i j, normMatrixCStarCoronaMk (fun n ↦ X n) (a i j) = x i j)
    (hb : ∀ i j, normMatrixCStarCoronaMk (fun n ↦ X n) (b i j) = y i j)
    (i j : I) :
    normMatrixCStarCoronaMk (fun n ↦ X n) (∑ k : I, a i k * b k j)
      = (x * y) i j := by
  rw [map_sum, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [map_mul, ha, hb]

/-- The corona class of the identity's entries. -/
theorem mk_one_entry (i j : I) :
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
theorem mul_eq_one_symm_matrixCorona [Nonempty I]
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
  have hMb0 : (0 : ℝ) ≤ ∑ i : I, ∑ j : I, ‖b i j‖ :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ norm_nonneg _
  have hhalf : ∀ᶠ n in (cofinite : Filter ℕ),
      ‖assemble X a n * assemble X b n - 1‖ ≤ (1 / 2 : ℝ) := by
    have hnear := (Metric.tendsto_nhds.mp hAB) (1 / 2 : ℝ) (by norm_num)
    filter_upwards [hnear] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  have hBA : Tendsto (fun n ↦ ‖assemble X b n * assemble X a n - 1‖) cofinite
      (nhds 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ ?_
    · filter_upwards [hhalf] with n hn
      refine le_trans
        (UltraproductDedekindFinite.norm_swap_sub_one_le
          (Y := I × X n) inferInstance (assemble X a n) (assemble X b n) hn) ?_
      have h1 : ‖assemble X a n‖ * ‖assemble X b n‖ ≤
          (∑ i : I, ∑ j : I, ‖a i j‖) * (∑ i : I, ∑ j : I, ‖b i j‖) :=
        mul_le_mul (norm_assemble_le X a n) (norm_assemble_le X b n)
          (norm_nonneg _) hMa0
      nlinarith [norm_nonneg (assemble X a n), norm_nonneg (assemble X b n),
        norm_nonneg (assemble X a n * assemble X b n - 1)]
    · have hc := hAB.const_mul
        (2 * (∑ i : I, ∑ j : I, ‖a i j‖) * (∑ i : I, ∑ j : I, ‖b i j‖))
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

end MatrixCoronaFinite
end GroupApproximation
