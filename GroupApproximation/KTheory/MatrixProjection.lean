import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Fin.Basic
import GroupApproximation.Analysis.FiniteCStarMurrayVonNeumann

/-!
# Block sums of matrix projections, and the moves `K`-theory is built from

This is the floor under the projection picture of topological `K`-theory.  In
that picture a complex vector bundle over a compact Hausdorff `X` *is* a
projection

  `p : Matrix (Fin N) (Fin N) C(X, ℂ)`,

bundle isomorphism *is* Murray--von Neumann equivalence of projections in the
matrix algebra, and the direct sum of bundles *is* the block-diagonal sum of
projections.  Nothing in this file knows any of that: everything below is
stated for a bare `*`-ring `A`, because the three facts `K`-theory actually
needs -- that a block sum of projections is a projection, that Murray--von
Neumann equivalence is additive under block sums, and that it survives
reindexing -- are pure `*`-ring algebra and hold verbatim over `C(X, ℂ)`.

`Analysis/KKTheoryKGroups.lean` records, in as many words, that this layer was
the reason the repository could not build `K₀` in its projection picture:

> The repository has the equivalence relation (`MurrayVonNeumannEquiv`) but not
> the monoid: assembling it needs block-diagonal sums, padding maps between
> matrix sizes, and permutation unitaries realizing commutativity, none of
> which exists here.

This file supplies the first two, and dispenses with the third: every
permutation move is realized as a `Matrix.submatrix` along an `Equiv`, and
`murrayVonNeumannEquiv_submatrix` transports the equivalence along it.  No
permutation matrix is ever written down, and no unitary group is needed.

## Two additions to `MurrayVonNeumannEquiv`

The relation itself already lives in `Analysis/FiniteCStarMurrayVonNeumann.lean`
with `refl`, `symm` and `of_isometry_conjugate`.  Transitivity was missing --
that file never needed it -- and it is not free: the composite implementer
`w * v` satisfies `star (w * v) * (w * v) = p * p`, so transitivity holds on
*idempotents*, not on arbitrary pairs satisfying the two implementer
identities.  The hypotheses below say exactly that, and no more: only `p` and
`r` have to be idempotent, never `q`.

## Design note: why `Fin` and not an arbitrary finite index

`Matrix.fromBlocks` is indexed by `Fin m ⊕ Fin n`, which is not a `Fin`, so a
`Fin`-indexed block sum has to be reindexed along `finSumFinEquiv`.  The
alternative -- carrying an arbitrary `Fintype` index and letting `⊕` be the
sum -- makes the block algebra free but pushes the `K`-groups up a universe and
loses the literal match with the campaign's model of a bundle, which is
`Fin N`-indexed.  The reindexing is paid for once, here.
-/

namespace GroupApproximation

open Matrix

section MurrayVonNeumann

variable {A : Type*}

/-- **Murray--von Neumann equivalence is transitive on idempotents.**

If `v` implements `p ∼ q` and `w` implements `q ∼ r`, then `w * v` implements
`p ∼ r`: the middle projection is absorbed by

  `star (w * v) * (w * v) = star v * (star w * w) * v = star v * (v * star v) * v
     = (star v * v) * (star v * v) = p * p`,

and symmetrically `(w * v) * star (w * v) = r * r`.  So the composite is an
implementer exactly when `p` and `r` are idempotent.  The middle projection `q`
carries no hypothesis: it is only ever used through the two implementer
identities, which is why this is stated for a `Semigroup` with `StarMul` and
not for a C-star algebra. -/
theorem MurrayVonNeumannEquiv.trans [Semigroup A] [StarMul A] {p q r : A}
    (hp : IsIdempotentElem p) (hr : IsIdempotentElem r)
    (h₁ : MurrayVonNeumannEquiv p q) (h₂ : MurrayVonNeumannEquiv q r) :
    MurrayVonNeumannEquiv p r := by
  obtain ⟨v, hv₁, hv₂⟩ := h₁
  obtain ⟨w, hw₁, hw₂⟩ := h₂
  refine ⟨w * v, ?_, ?_⟩
  · have h₃ : star (w * v) * (w * v) = star v * (star w * w) * v := by
      rw [star_mul]; simp only [mul_assoc]
    have h₄ : star v * (star w * w) * v = star v * v * (star v * v) := by
      rw [hw₁, ← hv₂]; simp only [mul_assoc]
    rw [h₃, h₄, hv₁, hp.eq]
  · have h₃ : (w * v) * star (w * v) = w * (v * star v) * star w := by
      rw [star_mul]; simp only [mul_assoc]
    have h₄ : w * (v * star v) * star w = w * star w * (w * star w) := by
      rw [hv₂, ← hw₁]; simp only [mul_assoc]
    rw [h₃, h₄, hw₂, hr.eq]

/-- Murray--von Neumann equivalence is preserved by any map that is
multiplicative and `star`-preserving.  Neither additivity nor continuity is
used: the implementer is transported verbatim. -/
theorem MurrayVonNeumannEquiv.map {B F : Type*} [Mul A] [Star A] [Mul B] [Star B]
    [FunLike F A B] [MulHomClass F A B] [StarHomClass F A B] {p q : A}
    (h : MurrayVonNeumannEquiv p q) (f : F) :
    MurrayVonNeumannEquiv (f p) (f q) := by
  obtain ⟨v, hv₁, hv₂⟩ := h
  exact ⟨f v, by rw [← hv₁, map_mul, map_star], by rw [← hv₂, map_mul, map_star]⟩

end MurrayVonNeumann

namespace KTheory

variable {A : Type*} {m n N M : ℕ}

section Defs

variable [Zero A]

/-- **The block-diagonal sum** of a square matrix of size `m` and a square
matrix of size `n`, reindexed along `finSumFinEquiv` to a square matrix of size
`m + n`.

Over `A = C(X, ℂ)` and for projections this is the direct sum of the two
vector bundles they present. -/
def blockSum (p : Matrix (Fin m) (Fin m) A) (q : Matrix (Fin n) (Fin n) A) :
    Matrix (Fin (m + n)) (Fin (m + n)) A :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p 0 0 q)

theorem blockSum_apply_castAdd_castAdd (p : Matrix (Fin m) (Fin m) A)
    (q : Matrix (Fin n) (Fin n) A) (i j : Fin m) :
    blockSum p q (Fin.castAdd n i) (Fin.castAdd n j) = p i j := by
  simp [blockSum, Matrix.submatrix_apply]

theorem blockSum_apply_natAdd_natAdd (p : Matrix (Fin m) (Fin m) A)
    (q : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    blockSum p q (Fin.natAdd m i) (Fin.natAdd m j) = q i j := by
  simp [blockSum, Matrix.submatrix_apply]

@[simp]
theorem blockSum_zero_zero :
    blockSum (0 : Matrix (Fin m) (Fin m) A) (0 : Matrix (Fin n) (Fin n) A) = 0 := by
  simp [blockSum]

end Defs

section Ring

variable [NonUnitalNonAssocSemiring A]

/-- **Block sums multiply blockwise.**  This is the identity that makes the
direct sum of bundles a monoid operation on projections. -/
@[simp]
theorem blockSum_mul_blockSum (p₁ p₂ : Matrix (Fin m) (Fin m) A)
    (q₁ q₂ : Matrix (Fin n) (Fin n) A) :
    blockSum p₁ q₁ * blockSum p₂ q₂ = blockSum (p₁ * p₂) (q₁ * q₂) := by
  simp [blockSum, Matrix.fromBlocks_multiply]

variable [StarRing A]

/-- Block sums are `star`-compatible: the adjoint of a block sum is the block
sum of the adjoints. -/
@[simp]
theorem star_blockSum (p : Matrix (Fin m) (Fin m) A) (q : Matrix (Fin n) (Fin n) A) :
    star (blockSum p q) = blockSum (star p) (star q) := by
  simp [blockSum, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]

/-- **A block sum of projections is a projection.** -/
theorem isStarProjection_blockSum {p : Matrix (Fin m) (Fin m) A}
    {q : Matrix (Fin n) (Fin n) A} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (blockSum p q) := by
  refine ⟨?_, ?_⟩
  · show blockSum p q * blockSum p q = blockSum p q
    rw [blockSum_mul_blockSum, hp.isIdempotentElem.eq, hq.isIdempotentElem.eq]
  · show star (blockSum p q) = blockSum p q
    rw [star_blockSum, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]

/-- The zero matrix of any size is a projection: the zero bundle. -/
theorem isStarProjection_zero_matrix :
    IsStarProjection (0 : Matrix (Fin m) (Fin m) A) :=
  IsStarProjection.zero _

/-- **Murray--von Neumann equivalence is additive under block sums.**

Over `C(X, ℂ)` this is the statement that isomorphic bundles have isomorphic
direct sums, and it is the reason the quotient by Murray--von Neumann
equivalence carries an addition at all.  The implementer of the sum is the
block sum of the implementers -- no projection hypothesis is needed. -/
theorem murrayVonNeumannEquiv_blockSum {p₁ p₂ : Matrix (Fin m) (Fin m) A}
    {q₁ q₂ : Matrix (Fin n) (Fin n) A}
    (hp : MurrayVonNeumannEquiv p₁ p₂) (hq : MurrayVonNeumannEquiv q₁ q₂) :
    MurrayVonNeumannEquiv (blockSum p₁ q₁) (blockSum p₂ q₂) := by
  obtain ⟨v, hv₁, hv₂⟩ := hp
  obtain ⟨w, hw₁, hw₂⟩ := hq
  refine ⟨blockSum v w, ?_, ?_⟩
  · rw [star_blockSum, blockSum_mul_blockSum, hv₁, hw₁]
  · rw [star_blockSum, blockSum_mul_blockSum, hv₂, hw₂]

/-- **Murray--von Neumann equivalence survives reindexing.**

Reindexing along an `Equiv` is conjugation by a permutation unitary, but no
permutation matrix appears: the implementer is reindexed along the same
`Equiv`, and `Matrix.submatrix_mul_equiv` does the rest.  Every commutativity
and associativity move for `blockSum` is an instance of this lemma. -/
theorem murrayVonNeumannEquiv_submatrix {p q : Matrix (Fin N) (Fin N) A}
    (e : Fin M ≃ Fin N) (h : MurrayVonNeumannEquiv p q) :
    MurrayVonNeumannEquiv (p.submatrix e e) (q.submatrix e e) := by
  obtain ⟨v, hv₁, hv₂⟩ := h
  refine ⟨v.submatrix e e, ?_, ?_⟩
  · simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv]
    rw [← Matrix.star_eq_conjTranspose, hv₁]
  · simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv]
    rw [← Matrix.star_eq_conjTranspose, hv₂]

/-- Reindexing preserves projections. -/
theorem isStarProjection_submatrix {p : Matrix (Fin N) (Fin N) A}
    (e : Fin M ≃ Fin N) (hp : IsStarProjection p) :
    IsStarProjection (p.submatrix e e) := by
  refine ⟨?_, ?_⟩
  · show p.submatrix e e * p.submatrix e e = p.submatrix e e
    rw [Matrix.submatrix_mul_equiv, hp.isIdempotentElem.eq]
  · show star (p.submatrix e e) = p.submatrix e e
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
    rw [← Matrix.star_eq_conjTranspose, hp.isSelfAdjoint.star_eq]

end Ring

end KTheory

end GroupApproximation
