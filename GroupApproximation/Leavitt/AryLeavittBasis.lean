import GroupApproximation.Leavitt.AryDegreeZeroUnits
import GroupApproximation.Meta.AxiomGuard

/-!
# Linear independence of the balanced Leavitt monomials

`Manuscript/MFRecognition/LeavittSeedPresentation.lean` carries the reduced
basis of the Leavitt algebra as a **cited input** ("Bergman, the diamond lemma
for ring theory, together with the standard reduced basis of the Leavitt
algebra.  Stated, never established here"), and a search of the tree finds no
`LinearIndependent` result about Leavitt monomials at any arity.  Spanning is
everywhere (`AryNormalForm.span_monomialSet_eq_top`); independence is nowhere.

This module proves the **degree-zero case** of independence, at every arity and
without the diamond lemma:

> for every field `k`, every `d` with `L_k(1,d)` nontrivial and every depth `n`,
> the `d^{2n}` balanced monomials `s_α t_β` with `|α| = |β| = n` are linearly
> independent over `k`.

Equivalently `M_{d^n}(k)` embeds unitally in `L_k(1,d)`, matrix unit `E_{αβ}`
going to `s_α t_β`.

## Why this needs no combinatorics at all

The whole content is that `A ≅ M_{ιⁿ}(A)` is an isomorphism, which
`CompleteMatrixFamily.matrixRingEquiv` already is, and that `k → A` is injective,
which holds because `k` is a field and `A` is nontrivial.  Composing,

    `M_{ιⁿ}(k) → M_{ιⁿ}(A) ≅ A`

is an injective ring homomorphism sending `E_{αβ}` to `s_α t_β`, and the matrix
units are a `k`-basis of the source.  No normal form, no rewriting system, no
faithfulness of a representation.

## What this is not

It is **not** the reduced basis.  The reduced basis is about all monomials
`s_α t_β` with `|α| ≠ |β|` allowed and the relation
`s_{α(d-1)}t_{β(d-1)} = s_α t_β - ∑_{i<d-1} s_{αi}t_{βi}` used to cut the
spanning set down; that statement needs the `ℤ`-grading to separate degrees and
then this result inside each degree.  What is proved here is the degree-zero
layer, which is the layer every `K₁` argument in this repository actually uses
(`AryDegreeZeroUnits`, `AryGradingSpans`, `AryWindowReduction`).
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

open scoped BigOperators

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

section Embedding

variable {k : Type*} [CommRing k] [Algebra k A]

/-- The matrix ring over the ground ring, pushed into `A` along the family:
`E_{ij} ↦ s_i t_j`. -/
noncomputable def matrixEmbedding : Matrix ι ι k →+* A :=
  F.matrixRingEquiv.toRingHom.comp ((algebraMap k A).mapMatrix)

theorem matrixEmbedding_apply (M : Matrix ι ι k) :
    F.matrixEmbedding M =
      ∑ i, ∑ j, F.left i * algebraMap k A (M i j) * F.right j := rfl

end Embedding

section Independence

variable {k : Type*} [Field k] [Algebra k A]

/-- **The embedding of the matrix ring is injective** over a field, as soon as
`A` is nontrivial. -/
theorem matrixEmbedding_injective [Nontrivial A] :
    Function.Injective (F.matrixEmbedding (k := k)) := by
  intro M N h
  have h' : (algebraMap k A).mapMatrix M = (algebraMap k A).mapMatrix N :=
    F.matrixRingEquiv.injective h
  ext i j
  exact (algebraMap k A).injective (congrFun (congrFun h' i) j)

/-- **The `|ι|²` products `s_i t_j` are linearly independent over `k`.** -/
theorem linearIndependent_left_mul_right [Nontrivial A] :
    LinearIndependent k (fun p : ι × ι ↦ F.left p.1 * F.right p.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  have hsum : ∑ q : ι × ι, g q • (F.left q.1 * F.right q.2) =
      F.matrixRingEquiv (Matrix.of fun i j ↦ algebraMap k A (g (i, j))) := by
    rw [matrixRingEquiv_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    show g (i, j) • (F.left i * F.right j) =
      F.left i * algebraMap k A (g (i, j)) * F.right j
    rw [Algebra.smul_def, ← mul_assoc, Algebra.commutes]
  rw [hsum] at hg
  have hzero : (Matrix.of fun i j ↦ algebraMap k A (g (i, j))) = 0 := by
    apply F.matrixRingEquiv.injective
    rw [hg, map_zero]
  have hentry : algebraMap k A (g p) = 0 := by
    have h := congrFun (congrFun hzero p.1) p.2
    rw [Matrix.zero_apply] at h
    exact h
  exact (algebraMap k A).injective (by rw [hentry, map_zero])

/-- **The balanced monomials at depth `n` are linearly independent.**  This is
the previous statement for the depth-`n` power family, whose left and right
families are the words of length `n`. -/
theorem linearIndependent_levelMonomials [Nontrivial A] (n : ℕ) :
    LinearIndependent k (fun p : (Fin n → ι) × (Fin n → ι) ↦
      F.wordS (List.ofFn p.1) * F.wordT (List.ofFn p.2)) :=
  (F.powerFamily n).linearIndependent_left_mul_right

end Independence

end CompleteMatrixFamily

/-! ### The Leavitt specialisation -/

namespace AryLeavitt

variable (k : Type) [Field k] (d : ℕ)

/-- **`M_{d^n}(k)` embeds in `L_k(1,d)`**, for every field, every `d ≥ 2` and
every depth `n`, by `E_{αβ} ↦ s_α t_β`. -/
theorem matrixEmbedding_injective (hd : 2 ≤ d) (n : ℕ) :
    Function.Injective
      (((family k d).powerFamily n).matrixEmbedding (k := k)) := by
  haveI : NeZero d := ⟨by omega⟩
  exact CompleteMatrixFamily.matrixEmbedding_injective _

/-- **The balanced monomials of `L_k(1,d)` at depth `n` are linearly
independent over `k`**, for every field and every `d ≥ 2`.

This is the first linear-independence statement about Leavitt monomials on the
tree; everything else about the monomials is spanning. -/
theorem linearIndependent_levelMonomials (hd : 2 ≤ d) (n : ℕ) :
    LinearIndependent k (fun p : (Fin n → Fin d) × (Fin n → Fin d) ↦
      (family k d).wordS (List.ofFn p.1) *
        (family k d).wordT (List.ofFn p.2)) := by
  haveI : NeZero d := ⟨by omega⟩
  exact (family k d).linearIndependent_levelMonomials n

end AryLeavitt
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.matrixEmbedding_injective
#audit_axioms
  GroupApproximation.CompleteMatrixFamily.linearIndependent_left_mul_right
#audit_axioms
  GroupApproximation.CompleteMatrixFamily.linearIndependent_levelMonomials
#audit_axioms GroupApproximation.AryLeavitt.matrixEmbedding_injective
#audit_axioms GroupApproximation.AryLeavitt.linearIndependent_levelMonomials
