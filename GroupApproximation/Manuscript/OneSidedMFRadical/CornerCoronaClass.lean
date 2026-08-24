import GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCorner
import GroupApproximation.Analysis.FilterMatrixCStarCorona

/-!
# The corona class of the corner representation

`non_mf_groups_exist.tex`, Lemma `lem:central-corona-corner`, last clause:

> ... after passing to an infinite coordinate subsequence, there are nonzero
> projections `q_n ∈ M_{d_n}(ℂ)` and an operator-norm asymptotic
> representation `W_n : G → U(q_n M_{d_n}(ℂ) q_n)` **whose corona class is the
> corner representation `g ↦ q rho(g)`**.

`Manuscript/OneSidedMFRadical/CentralCoronaCorner` delivers that last clause
as two facts stated over *different* index sets: an identity
`[Q V_g Q] = q rho(g)` in the corona over all coordinates `n`, and a
convergence `‖W_k(g) − q_k V_k(g) q_k‖ → 0` along the retained subsequence
`φ`.  Neither one, nor the pair, is the printed sentence: nothing there names
a corona class of `(W_n)`.

This file composes them.  Two constructions are needed, and both are the
identifications the printed proof itself makes.

## The corner is `q_n M_{d_n}(ℂ) q_n`, not an abstract `M_{r_n}(ℂ)`

`PrintedCornerCompression` realizes the corner as the principal block of the
eigenbasis of `q_n`, so the corner unitaries `W_n(g)` are matrices over a
coordinate subtype.  `cornerEmbed` puts them back where the print has them:
zero-extend the block and conjugate back by the eigenbasis unitary.  It is an
isometric star-embedding (`norm_cornerEmbed`, `cornerEmbed_mul`,
`cornerEmbed_conjTranspose`) whose image is the corner, and it carries the
uncorrected compression to the printed `q_n V_n(g) q_n`
(`cornerEmbed_cornerCompression`).  That is the printed identification
`q_n M_{d_n}(ℂ) q_n ≅ M_{r_n}(ℂ)`, used in the direction the sentence needs.

## "After passing to a subsequence" is a map of coronas

Retaining an infinite set of coordinates replaces the corona over `(d_n)` by
the corona over `(d_{φ k})`.  `coronaRestrict` is the induced star-epimorphism
between them: precomposition with `φ` preserves boundedness and carries null
sequences to null sequences because `φ` tends to infinity.  The printed
`q rho(g)`, read after the coordinates are discarded, is
`coronaRestrict (q rho(g))`.

## What is proved

`manuscriptCornerCoronaClass` is the printed sentence with its final clause a
single equation in one algebra:

    [k ↦ cornerEmbed (W_k g)]  =  coronaRestrict (q rho(g))

in the corona over the retained coordinates.  Its proof consumes
`manuscriptCentralCoronaCorner` unchanged; the new content is exactly the
bridge that the two uncomposed facts were missing.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix Topology
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

/-- **The zero extension of a principal block is the two-sided cut.** -/
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

/-- **Zero extension is contractive.**  The extension acts as `C` on the
retained coordinates and kills the rest. -/
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

/-- **Zero extension is isometric.**  Its principal block is the original
matrix, and principal blocks are contractive. -/
theorem norm_blockExtend {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p : Y → Prop) [DecidablePred p]
    (C : Matrix {i : Y // p i} {i : Y // p i} ℂ) :
    ‖blockExtend p C‖ = ‖C‖ := by
  refine le_antisymm (norm_blockExtend_le p C) ?_
  have h := norm_principalBlock_le p (blockExtend p C)
  rwa [principalBlock_blockExtend] at h

/-! ## The printed identification `q_n M_{d_n}(ℂ) q_n ≅ M_{r_n}(ℂ)` -/

/-- **The corner of `q`, as a subalgebra of the ambient matrices.**  A matrix
on the corner coordinates of `q` is zero-extended and conjugated back out of
the eigenbasis of `q`.  This is the printed identification
`q_n M_{d_n}(ℂ) q_n ≅ M_{r_n}(ℂ)`, in the direction that reads a corner
matrix as an ambient one. -/
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

/-- **The embedded compression is the printed `q V q`.**  This is the one
place the corner identification is used: `cornerCompression` is what the
development compresses to, and `q_n V_{g,n} q_n` is what the manuscript
writes. -/
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

/-! ## The corner representation, read inside the ambient matrices -/

/-- **The printed `W_n(g)`, viewed in `q_n M_{d_n}(ℂ) q_n ⊆ M_{d_n}(ℂ)`.** -/
def ambientCornerMap {G : Type*} [Group G] {model : ℕ → FiniteModel}
    (D : PrintedCornerData G model) (n : ℕ) (g : G) :
    Matrix (model n) (model n) ℂ :=
  cornerEmbed (D.qHermitian n)
    ((D.cornerMap n g : Matrix (D.cornerModel n) (D.cornerModel n) ℂ))

theorem norm_ambientCornerMap_le_one {G : Type*} [Group G]
    {model : ℕ → FiniteModel} (D : PrintedCornerData G model) (n : ℕ)
    (g : G) : ‖ambientCornerMap D n g‖ ≤ 1 := by
  rw [ambientCornerMap, norm_cornerEmbed]
  exact D.norm_cornerMap_le_one n g

/-- **The printed estimate, moved into the ambient matrices.**  The embedded
corner unitary differs from the printed compression `q_n V_{g,n} q_n` by
exactly the polar correction, whose norm is unchanged by the embedding. -/
theorem norm_ambientCornerMap_sub_compress_le {G : Type*} [Group G]
    {model : ℕ → FiniteModel} (D : PrintedCornerData G model) (n : ℕ)
    (g : G) :
    ‖ambientCornerMap D n g -
        D.q n * (D.V n g : Matrix (model n) (model n) ℂ) * D.q n‖
      ≤ ‖(D.cornerMap n g : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
          - D.compress n g‖ := by
  have hcompress : cornerEmbed (D.qHermitian n) (D.compress n g)
      = D.q n * (D.V n g : Matrix (model n) (model n) ℂ) * D.q n :=
    cornerEmbed_cornerCompression (D.qHermitian n) (D.qIdem n)
      ((D.V n g : Matrix (model n) (model n) ℂ))
  rw [← hcompress, ambientCornerMap, ← cornerEmbed_sub]
  exact le_of_eq (norm_cornerEmbed (D.qHermitian n) _)

/-- **The corner representation as a bounded matrix sequence.**  Its class is
the corona class the printed lemma names. -/
def ambientCornerSeq {G : Type*} [Group G] {model : ℕ → FiniteModel}
    (D : PrintedCornerData G model) (g : G) :
    BoundedMatrixSequence (fun n ↦ model n) :=
  ⟨fun n ↦ ambientCornerMap D n g, memℓp_infty ⟨1, by
    rintro _ ⟨n, rfl⟩
    exact norm_ambientCornerMap_le_one D n g⟩⟩

theorem ambientCornerSeq_apply {G : Type*} [Group G]
    {model : ℕ → FiniteModel} (D : PrintedCornerData G model) (g : G)
    (n : ℕ) : ambientCornerSeq D g n = ambientCornerMap D n g := rfl

/-! ## Discarding coordinates, as a map of coronas -/

/-- Restriction of a bounded matrix sequence to a coordinate subsequence. -/
def restrictSeq (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (φ : ℕ → ℕ) :
    BoundedMatrixSequence (fun n ↦ X n) →⋆ₐ[ℂ]
      BoundedMatrixSequence (fun k ↦ X (φ k)) where
  toFun a := ⟨fun k ↦ a (φ k), memℓp_infty ⟨‖a‖, by
    rintro _ ⟨k, rfl⟩
    exact boundedMatrixSequence_coord_norm_le (fun n ↦ X n) a (φ k)⟩⟩
  map_one' := by ext k i j; rfl
  map_mul' a b := by ext k i j; rfl
  map_zero' := by ext k i j; rfl
  map_add' a b := by ext k i j; rfl
  commutes' z := by ext k i j; rfl
  map_star' a := by ext k i j; rfl

theorem restrictSeq_apply (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (φ : ℕ → ℕ)
    (a : BoundedMatrixSequence (fun n ↦ X n)) (k : ℕ) :
    restrictSeq X φ a k = a (φ k) := rfl

theorem restrictSeq_star (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (φ : ℕ → ℕ)
    (a : BoundedMatrixSequence (fun n ↦ X n)) :
    restrictSeq X φ (star a) = star (restrictSeq X φ a) :=
  map_star (restrictSeq X φ) a

/-- A subsequence of a sequence that is null along `cofinite` is null along
`cofinite`, because a strictly monotone reindexing tends to infinity.  This is
the only place the subsequence hypothesis is used. -/
theorem isNullMatrixSequence_restrictSeq (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] {φ : ℕ → ℕ}
    (hφ : StrictMono φ) {a : BoundedMatrixSequence (fun n ↦ X n)}
    (ha : IsNullMatrixSequence (fun n ↦ X n) cofinite a) :
    IsNullMatrixSequence (fun k ↦ X (φ k)) cofinite (restrictSeq X φ a) := by
  rw [IsNullMatrixSequence, Nat.cofinite_eq_atTop] at ha ⊢
  exact (ha.comp hφ.tendsto_atTop).congr fun k ↦ rfl

/-- Restriction followed by the quotient map on the retained coordinates. -/
def restrictSeqCoronaQuotient (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (φ : ℕ → ℕ) :
    BoundedMatrixSequence (fun n ↦ X n) →⋆ₐ[ℂ]
      NormMatrixCStarCorona (fun k ↦ X (φ k)) :=
  (normMatrixCStarCoronaQuotient (fun k ↦ X (φ k))).comp (restrictSeq X φ)

@[simp] theorem restrictSeqCoronaQuotient_apply
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (φ : ℕ → ℕ)
    (a : BoundedMatrixSequence (fun n ↦ X n)) :
    restrictSeqCoronaQuotient X φ a =
      normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (restrictSeq X φ a) :=
  rfl

theorem restrictSeqCoronaQuotient_eq_zero_of_null
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (a : BoundedMatrixSequence (fun n ↦ X n))
    (ha : IsNullMatrixSequence (fun n ↦ X n) cofinite a) :
    restrictSeqCoronaQuotient X φ a = 0 := by
  rw [restrictSeqCoronaQuotient_apply]
  apply (normMatrixCStarCoronaMk_eq_zero_iff (fun k ↦ X (φ k)) _).mpr
  exact isNullMatrixSequence_restrictSeq X hφ ha

/-- **"Retain those coordinates", as a homomorphism of coronas.**  Discarding
all coordinates outside the range of `φ` replaces the corona over `(d_n)` by
the corona over `(d_{φ k})`, and the replacement is induced by restriction of
sequences.  `coronaRestrict_star` records that it is a star-homomorphism. -/
def coronaRestrict (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (φ : ℕ → ℕ)
    (hφ : StrictMono φ) :
    NormMatrixCStarCorona (fun n ↦ X n) →+*
      NormMatrixCStarCorona (fun k ↦ X (φ k)) := by
  change FilterMatrixCStarCorona (fun n ↦ X n) cofinite →+*
    NormMatrixCStarCorona (fun k ↦ X (φ k))
  exact (filterMatrixCStarCoronaLift (fun n ↦ X n) cofinite
    (restrictSeqCoronaQuotient X φ)
    (fun a ha ↦ restrictSeqCoronaQuotient_eq_zero_of_null X hφ a ha)).toRingHom

@[simp] theorem coronaRestrict_mk (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (a : BoundedMatrixSequence (fun n ↦ X n)) :
    coronaRestrict X φ hφ (normMatrixCStarCoronaMk (fun n ↦ X n) a)
      = normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (restrictSeq X φ a) :=
  by
    change filterMatrixCStarCoronaLift (fun n ↦ X n) cofinite
      (restrictSeqCoronaQuotient X φ)
      (fun b hb ↦ restrictSeqCoronaQuotient_eq_zero_of_null X hφ b hb)
      (filterMatrixCStarCoronaMk (fun n ↦ X n) cofinite a) = _
    rw [filterMatrixCStarCoronaLift_mk, restrictSeqCoronaQuotient_apply]

theorem coronaRestrict_star (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    coronaRestrict X φ hφ (star x) = star (coronaRestrict X φ hφ x) := by
  obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) x
  rw [normMatrixCStarCorona_star_mk, coronaRestrict_mk, restrictSeq_star,
    coronaRestrict_mk, normMatrixCStarCorona_star_mk]

/-! ## The printed lemma, with its final clause composed -/

/-- **Lemma `lem:central-corona-corner`, whole.**

> Let `rho : G → U(𝒬_d)` be a homomorphism from a countable group, and let
> `q ∈ 𝒬_d` be a nonzero projection commuting with `rho(G)`.  Then, after
> passing to an infinite coordinate subsequence, there are nonzero
> projections `q_n ∈ M_{d_n}(ℂ)` and an operator-norm asymptotic
> representation `W_n : G → U(q_n M_{d_n}(ℂ) q_n)` whose corona class is the
> corner representation `g ↦ q rho(g)`.

`φ` is the infinite coordinate subsequence, `Q` the projection lift of `q`,
`D.q` the printed `q_n` — nonzero at every retained stage — and
`D.cornerRepresentation` the printed `(W_n)`, an `OpAlmostRepresentation`
whose maps are `D.cornerMap`.

The final clause is one equation, in the corona over the retained
coordinates: the class of the sequence of corner unitaries, read inside
`q_n M_{d_n}(ℂ) q_n` by the printed identification, is the image of
`q rho(g)` under the restriction map that discarding coordinates induces.
Both sides are elements of `NormMatrixCStarCorona (fun k ↦ X (φ k))`; no
clause of this statement is a limit over one index set compared with an
identity over another. -/
def CornerCoronaClass : Prop :=
  ∀ (G : Type) [Group G] [Countable G]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (q : NormMatrixCStarCorona (fun n ↦ X n)),
    star q = q → q * q = q → q ≠ 0 →
    (∀ g : G, ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) * q =
      q * ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n))) →
    ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ)
      (Q : BoundedMatrixSequence (fun n ↦ X n))
      (D : PrintedCornerData G (fun k ↦ X (φ k))),
      (∀ n, IsOrthogonalProjectionMatrix
        ((Q : ∀ n, Matrix (X n) (X n) ℂ) n)) ∧
      normMatrixCStarCoronaMk (fun n ↦ X n) Q = q ∧
      (∀ k, D.q k = (Q : ∀ n, Matrix (X n) (X n) ℂ) (φ k)) ∧
      (∀ k, D.q k ≠ 0) ∧
      (∀ k, 0 < Fintype.card (D.cornerModel k)) ∧
      (∀ k g, HEq (D.cornerRepresentation.map k g) (D.cornerMap k g)) ∧
      (∀ g : G,
        normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (ambientCornerSeq D g)
          = coronaRestrict X φ hφ
              (q * ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
                NormMatrixCStarCorona (fun n ↦ X n))))

/-- Closed proof of the composed central-corona-corner lemma. -/
theorem manuscriptCornerCoronaClass : CornerCoronaClass := by
  intro G _ _ X _ rho q hqstar hqid hqne hcentral
  obtain ⟨Q, φ, D, hφmono, hQproj, hQmk, hDq, hDV, hcard, hHEq, hpair⟩ :=
    manuscriptCentralCoronaCorner G X rho q hqstar hqid hqne hcentral
  refine ⟨φ, hφmono, Q, D, hQproj, hQmk, hDq, D.q_ne_zero, hcard, hHEq, ?_⟩
  intro g
  obtain ⟨hclass, hcorr⟩ := hpair g
  set Wg : BoundedMatrixSequence (fun n ↦ X n) :=
    Q * unitarySequenceBounded X (CollapseUnitaryLift.liftFam X rho g) * Q
    with hWg
  have hW : ∀ k, restrictSeq X φ Wg k
      = D.q k * (D.V k g : Matrix (X (φ k)) (X (φ k)) ℂ) * D.q k := by
    intro k
    rw [hWg, hDq k, hDV k g]
    ext i j
    rfl
  have hbound : ∀ k, ‖((ambientCornerSeq D g :
        BoundedMatrixSequence (fun k ↦ X (φ k))) - restrictSeq X φ Wg) k‖
      ≤ ‖(D.cornerMap k g : Matrix (D.cornerModel k) (D.cornerModel k) ℂ)
          - D.compress k g‖ := by
    intro k
    rw [lp.coeFn_sub, Pi.sub_apply, hW k]
    exact norm_ambientCornerMap_sub_compress_le D k g
  have hnull : IsNullMatrixSequence (fun k ↦ X (φ k)) cofinite
      ((ambientCornerSeq D g : BoundedMatrixSequence (fun k ↦ X (φ k)))
        - restrictSeq X φ Wg) := by
    rw [IsNullMatrixSequence, Nat.cofinite_eq_atTop]
    exact squeeze_zero' (Eventually.of_forall fun k ↦ norm_nonneg _)
      (Eventually.of_forall hbound) hcorr
  calc normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (ambientCornerSeq D g)
      = normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (restrictSeq X φ Wg) := by
        rw [← sub_eq_zero, ← map_sub]
        exact (normMatrixCStarCoronaMk_eq_zero_iff (fun k ↦ X (φ k)) _).mpr
          hnull
    _ = coronaRestrict X φ hφmono
          (normMatrixCStarCoronaMk (fun n ↦ X n) Wg) :=
        (coronaRestrict_mk X φ hφmono Wg).symm
    _ = coronaRestrict X φ hφmono
          (q * ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n))) := by rw [hclass]

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
