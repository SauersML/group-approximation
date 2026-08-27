import GroupApproximation.Analysis.CStarSliceBound

/-!
# Slices of the ideal span lie in the ideal

Toward proof-ledger row `SO.16`.  The Fubini identity the exactness argument
needs is

`closure (I ⊙ C) = {z | every slice of z lies in I}`,

and only one of its two inclusions is elementary.  This module proves that
one, at the algebraic level: **every second-variable slice of an element of
`I ⊙ C` lies in `I`**.

The proof is span induction and nothing else.  On a generator `b ⊗ₜ c` with
`b ∈ I` the coordinate slice is `⟪c, e_j⟫ • b`, which is in `I` because an
ideal is a submodule; the set of elements whose slice lies in `I` is a
submodule, so it contains the span.

## What this is and is not

This is the inclusion `I ⊙ C ⊆ {z | slices in I}`.  The *other* inclusion is
the slice map property, and it is **not** elementary and **not** proved here:
it fails for general C⋆-algebras, being tied to exactness of the ambient
algebra, which is the very thing the `SO.16` argument is trying to establish
about a subalgebra.  So this module moves no grade; it records the half of
Fubini that is free, so that whoever attacks the other half knows exactly
which half is missing.

`Analysis/CStarSliceBound.norm_sliceRight_vecFunctional_le` is what would
carry this statement from the algebraic tensor product to the minimal
completion, the slice being continuous and `I` closed.

## Manuscript status

Infrastructure toward `SO.16`; certifies no manuscript step.
-/

namespace GroupApproximation
namespace CStarTensor

open scoped TensorProduct

noncomputable section

variable {B C : Type u} [CStarAlgebra B] [CStarAlgebra C]

/-- The algebraic ideal span inside `B ⊗[ℂ] C`: the span of the elementary
tensors whose left leg lies in `I`. -/
def algIdealTensorSpan (I : Submodule ℂ B) : Submodule ℂ (B ⊗[ℂ] C) :=
  Submodule.span ℂ {z | ∃ b c, b ∈ I ∧ z = b ⊗ₜ[ℂ] c}

theorem tmul_mem_algIdealTensorSpan {I : Submodule ℂ B} {b : B} (hb : b ∈ I)
    (c : C) : (b ⊗ₜ[ℂ] c : B ⊗[ℂ] C) ∈ algIdealTensorSpan I :=
  Submodule.subset_span ⟨b, c, hb, rfl⟩

/-- **The easy half of Fubini.**  Every coordinate slice of an element of
`I ⊙ C` lies in `I`. -/
theorem coordSlice_mem_of_mem_algIdealTensorSpan {I : Submodule ℂ B}
    {κ : Type*} (e : Module.Basis κ ℂ C) (j : κ)
    {z : B ⊗[ℂ] C} (hz : z ∈ algIdealTensorSpan I) :
    coordSlice e j z ∈ I := by
  -- the elements whose slice lands in `I` form a submodule
  refine Submodule.span_induction (p := fun w _ ↦ coordSlice e j w ∈ I)
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨b, c, hb, rfl⟩
    rw [coordSlice_tmul]
    exact I.smul_mem _ hb
  · rw [map_zero]
    exact I.zero_mem
  · intro w w' _ _ hw hw'
    rw [map_add]
    exact I.add_mem hw hw'
  · intro a w _ hw
    rw [map_smul]
    exact I.smul_mem _ hw

end

end CStarTensor
end GroupApproximation
