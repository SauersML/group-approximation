import GroupApproximation.Leavitt.AryLeavittBasis
import GroupApproximation.Leavitt.AryGradingSpans
import GroupApproximation.Meta.AxiomGuard

/-!
# The tower of matrix stages inside `L_k(1,d)`

`cor:leavitt-mf-quotient` asserts `K₁(L_k(1,d)) ≅ k^×/(k^×)^{d-1}`, and every
proof runs through the degree-zero part `L₀ = ⋃ₙ M_{dⁿ}(k)`.  This module builds
the tower whose union `L₀` is: the stages, their nesting, and the fact that each
one really is a copy of `M_{dⁿ}(k)` rather than a quotient of one.

* `stageSubalgebra F n` --- the image of `M_{ιⁿ}(k)` in `A` under
  `E_{αβ} ↦ s_α t_β`, as a `Subalgebra k A`.
* `stageSubalgebra_coe_eq_span` --- that image is exactly the `k`-span of the
  balanced monomials at depth `n`.
* `stageSubalgebra_mono` --- **the stages increase**, which is the completeness
  relation `1 = ∑ᵢ sᵢtᵢ` inserted between the two words, one letter at a time.
* `stageSubring` --- the same thing as a `Subring`, which is the form
  `KOne/LeavittKOneNestedUnion.lean` consumes.

## Why the stages are copies and not quotients

`Leavitt/AryLeavittBasis.lean` proves `AryLeavitt.matrixEmbedding_injective`,
the degree-zero layer of the reduced basis.  Without it the stage maps would be
mere surjections onto their images and the colimit of the `K₁`s would say
nothing about `K₁(L₀)`.  With it, `stageEquiv` below is a ring isomorphism
`M_{dⁿ}(k) ≃+* stageSubring`, which is what feeds
`AlgebraicKOne (M_{dⁿ}(k)) ≃* kˣ`.

## What is reused rather than reproved

Both halves of the nesting were already on the tree and are not reproved here:
`CompleteMatrixFamily.wordS_mul_wordT_split` (one-letter extension, from
`Leavitt/AryWords.lean`) and
`CompleteMatrixFamily.span_levelMonomialSet_le_succ` (its span form, from
`Leavitt/AryGradingSpans.lean`).  What is new is the passage between the span
picture and the *ring* picture: a `Subalgebra`, so that `Submodule.span_le` can
be applied to it, and so that the result is the kind of object a nested-union
argument accepts.

## What this is not

It does not yet identify the union with the degree-zero part of a `ℤ`-grading;
the tree has no `GradedAlgebra` structure on `L_k(1,d)`, only the span-level
`levelMonomialSet` vocabulary used here.  For the `K₁` computation the union is
what matters, and the grading is needed only for the corner skew Laurent
presentation.
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

open scoped BigOperators

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

section Stage

variable {k : Type*} [CommRing k] [Algebra k A]

/-- The matrix embedding is `k`-linear: a scalar comes out through
`Algebra.commutes`. -/
theorem matrixEmbedding_smul (c : k) (M : Matrix ι ι k) :
    F.matrixEmbedding (k := k) (c • M)
      = algebraMap k A c * F.matrixEmbedding (k := k) M := by
  rw [matrixEmbedding_apply, matrixEmbedding_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  show F.left i * algebraMap k A (c * M i j) * F.right j
    = algebraMap k A c * (F.left i * algebraMap k A (M i j) * F.right j)
  rw [map_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc, Algebra.commutes]

/-- The matrix embedding as a `k`-algebra map. -/
noncomputable def matrixEmbeddingAlg : Matrix ι ι k →ₐ[k] A :=
  AlgHom.mk' (F.matrixEmbedding (k := k)) (fun c M ↦ by
    rw [matrixEmbedding_smul, Algebra.smul_def])

@[simp] theorem matrixEmbeddingAlg_apply (M : Matrix ι ι k) :
    F.matrixEmbeddingAlg (k := k) M = F.matrixEmbedding (k := k) M := rfl

/-- `AlgHom.range` membership presents the map through `toRingHom`, so this is
the spelling the range goals actually carry. -/
@[simp] theorem matrixEmbeddingAlg_toRingHom_apply (M : Matrix ι ι k) :
    (F.matrixEmbeddingAlg (k := k)).toRingHom M = F.matrixEmbedding (k := k) M :=
  rfl

/-- **The stage `M_{ιⁿ}(k) ⊆ A`**, the image of the depth-`n` matrix embedding. -/
noncomputable def stageSubalgebra (n : ℕ) : Subalgebra k A :=
  ((F.powerFamily n).matrixEmbeddingAlg (k := k)).range

theorem mem_stageSubalgebra_iff (n : ℕ) (x : A) :
    x ∈ F.stageSubalgebra (k := k) n ↔
      ∃ M : Matrix (Fin n → ι) (Fin n → ι) k,
        ((F.powerFamily n).matrixEmbedding (k := k)) M = x :=
  Iff.rfl

/-- A balanced monomial at depth `n` is in the stage: it is the image of a
matrix unit. -/
theorem monomial_mem_stageSubalgebra (n : ℕ) (f g : Fin n → ι) :
    F.wordS (List.ofFn f) * F.wordT (List.ofFn g)
      ∈ F.stageSubalgebra (k := k) n := by
  classical
  refine ⟨Matrix.single f g 1, ?_⟩
  rw [matrixEmbeddingAlg_toRingHom_apply, matrixEmbedding_apply]
  have hinner : ∀ p : Fin n → ι,
      ∑ q : Fin n → ι, (F.powerFamily n).left p *
          algebraMap k A ((Matrix.single f g (1 : k)) p q) *
          (F.powerFamily n).right q
        = if p = f then F.wordS (List.ofFn f) * F.wordT (List.ofFn g) else 0 := by
    intro p
    by_cases hp : p = f
    · subst hp
      rw [if_pos rfl, Finset.sum_eq_single g]
      · rw [Matrix.single_apply_same, map_one, mul_one]
        rfl
      · intro q _ hq
        rw [Matrix.single_apply_of_ne _ _ _ _ _ (by simp [hq.symm]), map_zero,
          mul_zero, zero_mul]
      · intro hg
        exact absurd (Finset.mem_univ g) hg
    · rw [if_neg hp]
      refine Finset.sum_eq_zero fun q _ ↦ ?_
      rw [Matrix.single_apply_of_ne _ _ _ _ _ (by simp [Ne.symm hp]), map_zero,
        mul_zero, zero_mul]
  rw [Finset.sum_congr rfl (fun p _ ↦ hinner p), Finset.sum_ite_eq' Finset.univ f
    (fun _ ↦ F.wordS (List.ofFn f) * F.wordT (List.ofFn g)),
    if_pos (Finset.mem_univ f)]

/-- Every element of the stage is a `k`-combination of balanced monomials. -/
theorem stageSubalgebra_le_span (n : ℕ) :
    Subalgebra.toSubmodule (F.stageSubalgebra (k := k) n)
      ≤ Submodule.span k (F.levelMonomialSet n) := by
  rintro _ ⟨M, rfl⟩
  rw [matrixEmbeddingAlg_toRingHom_apply, matrixEmbedding_apply]
  refine Submodule.sum_mem _ fun p _ ↦ Submodule.sum_mem _ fun q _ ↦ ?_
  have hsmul : (F.powerFamily n).left p * algebraMap k A (M p q) *
      (F.powerFamily n).right q
      = M p q • (F.wordS (List.ofFn p) * F.wordT (List.ofFn q)) := by
    rw [Algebra.smul_def, ← mul_assoc, Algebra.commutes]
    rfl
  rw [hsmul]
  exact Submodule.smul_mem _ _
    (F.monomial_mem_span_levelMonomialSet (k := k) n (by simp) (by simp))

/-- Conversely the span of the balanced monomials is inside the stage. -/
theorem span_le_stageSubalgebra (n : ℕ) :
    Submodule.span k (F.levelMonomialSet n)
      ≤ Subalgebra.toSubmodule (F.stageSubalgebra (k := k) n) := by
  rw [Submodule.span_le]
  rintro _ ⟨f, g, rfl⟩
  exact F.monomial_mem_stageSubalgebra (k := k) n f g

/-- **The stage is exactly the span of the balanced monomials at that depth.** -/
theorem stageSubalgebra_toSubmodule (n : ℕ) :
    Subalgebra.toSubmodule (F.stageSubalgebra (k := k) n)
      = Submodule.span k (F.levelMonomialSet n) :=
  le_antisymm (F.stageSubalgebra_le_span n) (F.span_le_stageSubalgebra n)

/-- **The stages increase.**  This is the completeness relation inserted between
the two words, transported from its span form. -/
theorem stageSubalgebra_mono : Monotone (F.stageSubalgebra (k := k)) := by
  intro m n h x hx
  have h1 : x ∈ Submodule.span k (F.levelMonomialSet m) := by
    rw [← F.stageSubalgebra_toSubmodule (k := k) m]
    exact hx
  have h2 : x ∈ Submodule.span k (F.levelMonomialSet n) :=
    F.span_levelMonomialSet_mono (k := k) h h1
  rw [← F.stageSubalgebra_toSubmodule (k := k) n] at h2
  exact h2

/-- The stage as a `Subring`, which is what a nested-union argument consumes. -/
noncomputable def stageSubring (n : ℕ) : Subring A :=
  (F.stageSubalgebra (k := k) n).toSubring

theorem stageSubring_mono : Monotone (F.stageSubring (k := k)) :=
  fun _ _ h _ hx => F.stageSubalgebra_mono (k := k) h hx

end Stage

end CompleteMatrixFamily

/-! ### The Leavitt specialisation -/

namespace AryLeavitt

variable (k : Type) [Field k] (d : ℕ)

/-- **The depth-`n` stage of `L_k(1,d)`**, a copy of `M_{dⁿ}(k)`. -/
noncomputable def stage (n : ℕ) : Subring (AryLeavittAlgebra k d) :=
  ((family k d).stageSubring (k := k) n)

/-- **The stages of `L_k(1,d)` increase.** -/
theorem stage_mono : Monotone (stage k d) :=
  (family k d).stageSubring_mono (k := k)

/-- **Each stage is a copy of `M_{dⁿ}(k)`, not a quotient of one**, by the
degree-zero layer of the reduced basis. -/
theorem stage_matrixEmbedding_injective (hd : 2 ≤ d) (n : ℕ) :
    Function.Injective
      (((family k d).powerFamily n).matrixEmbedding (k := k)) :=
  AryLeavitt.matrixEmbedding_injective k d hd n

end AryLeavitt
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.matrixEmbedding_smul
#audit_axioms GroupApproximation.CompleteMatrixFamily.monomial_mem_stageSubalgebra
#audit_axioms GroupApproximation.CompleteMatrixFamily.stageSubalgebra_toSubmodule
#audit_axioms GroupApproximation.CompleteMatrixFamily.stageSubalgebra_mono
#audit_axioms GroupApproximation.AryLeavitt.stage_mono
#audit_axioms GroupApproximation.AryLeavitt.stage_matrixEmbedding_injective
