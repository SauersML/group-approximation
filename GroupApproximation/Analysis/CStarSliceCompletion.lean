import GroupApproximation.Analysis.CStarSliceBound

/-!
# The slice map on `A ⊗_min B`

Toward proof-ledger row `SO.16`.  `CStarSliceBound` proves the estimate

`‖sliceRight (vecFunctional φ ξ ξ') x‖ ≤ ‖ξ‖ * ‖ξ'‖ * ‖x‖_min`

for `x` in the *algebraic* tensor product, and the ledger note for that module
says what the estimate is for: it is what carries `sliceRight` from the
algebraic tensor product to the minimal completion.  This module performs that
carry.

`LinearMap.extendOfNorm` is the exact shape of the hypothesis: a linear map
`f` out of a bare module, a dense linear map `e` into a normed space, and a
bound `‖f x‖ ≤ C * ‖e x‖`.  Here `e` is `minTensorIn`, whose range is dense by
`denseRange_minTensorIn` and whose norm is `minTensorNorm` by
`norm_minTensorIn`, so the bound is literally the estimate above.

## What the extension buys

The easy half of Fubini --- every slice of an element of `A ⊙ J` lies in `J`
--- is an algebraic statement, and `CStarSliceIdeal` proves the mirror of it
for coordinate slices.  Its interest for `SO.16` is at the completion, since
the Fubini identity is about `A ⊗_min B` and not about the algebraic tensor
product, and an algebraic statement transfers only if the slice is continuous
and the ideal closed.  Both halves are now available:
`sliceRightMin` is continuous by construction and
`sliceRightMin_mem_of_mem_closure` is the transfer.

## What is still missing

The *other* inclusion of Fubini --- an element all of whose slices lie in `J`
lies in the closed span --- is the slice map property, is false for general
C⋆-algebras, and is not proved here or anywhere in the development.  So this
module moves no grade.  It records that the free half of Fubini now holds at
the completion, which is where the argument needs it, and leaves the trust
surface exactly where the ledger says it is.

## Manuscript status

Infrastructure toward `SO.16`; certifies no manuscript step.
-/

namespace GroupApproximation
namespace CStarTensor

open CStarState
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
  [Nontrivial A] [Nontrivial B]

/-! ## The canonical embedding as a plain linear map -/

variable (A B) in
/-- `minTensorIn` read as a linear map.  `LinearMap.extendOfNorm` wants the
dense map in this form, and the ⋆-algebra structure plays no part in the
extension. -/
def minTensorInL : (A ⊗[ℂ] B) →ₗ[ℂ] MinTensorProduct A B where
  toFun x := minTensorIn A B x
  map_add' x y := map_add (minTensorIn A B) x y
  map_smul' c x := map_smul (minTensorIn A B) c x

@[simp] theorem minTensorInL_apply (x : A ⊗[ℂ] B) :
    minTensorInL A B x = minTensorIn A B x := rfl

theorem norm_minTensorInL (x : A ⊗[ℂ] B) :
    ‖minTensorInL A B x‖ = minTensorNorm x :=
  norm_minTensorIn x

theorem denseRange_minTensorInL : DenseRange (minTensorInL A B) :=
  denseRange_minTensorIn

/-! ## The extended slice -/

/-- The estimate of `CStarSliceBound`, restated against the norm of the
embedding, which is the form the extension lemma consumes. -/
theorem norm_sliceRight_le_norm_minTensorInL (φ : State A) (ξ ξ' : φ.GNSSpace)
    (x : A ⊗[ℂ] B) :
    ‖sliceRight (vecFunctional φ.gnsRep ξ ξ') x‖
      ≤ (‖ξ‖ * ‖ξ'‖) * ‖minTensorInL A B x‖ := by
  rw [norm_minTensorInL]
  exact norm_sliceRight_vecFunctional_le φ ξ ξ' x

/-- **The slice map on `A ⊗_min B`.**  The vector-functional slice, extended
from the algebraic tensor product to the minimal completion by its own bound.
-/
def sliceRightMin (φ : State A) (ξ ξ' : φ.GNSSpace) :
    MinTensorProduct A B →L[ℂ] B :=
  LinearMap.extendOfNorm (sliceRight (vecFunctional φ.gnsRep ξ ξ'))
    (minTensorInL A B)

/-- The extension deserves the name: on the algebraic tensor product it is the
slice it extends. -/
@[simp] theorem sliceRightMin_minTensorIn (φ : State A) (ξ ξ' : φ.GNSSpace)
    (x : A ⊗[ℂ] B) :
    sliceRightMin φ ξ ξ' (minTensorIn A B x)
      = sliceRight (vecFunctional φ.gnsRep ξ ξ') x :=
  LinearMap.extendOfNorm_eq denseRange_minTensorInL
    ⟨‖ξ‖ * ‖ξ'‖, norm_sliceRight_le_norm_minTensorInL φ ξ ξ'⟩ x

/-- The bound survives the extension, pointwise. -/
theorem norm_sliceRightMin_le (φ : State A) (ξ ξ' : φ.GNSSpace)
    (z : MinTensorProduct A B) :
    ‖sliceRightMin φ ξ ξ' z‖ ≤ (‖ξ‖ * ‖ξ'‖) * ‖z‖ :=
  LinearMap.norm_extendOfNorm_apply_le denseRange_minTensorInL _
    (norm_sliceRight_le_norm_minTensorInL φ ξ ξ') z

/-! ## The free half of Fubini, at the completion -/

variable (A) in
/-- The algebraic span `A ⊙ J`: the elementary tensors whose **right** leg
lies in `J`.  `CStarSliceIdeal.algIdealTensorSpan` is the mirror image, on the
left leg, which is the one `coordSlice` reads. -/
def algIdealTensorSpanRight (J : Submodule ℂ B) : Submodule ℂ (A ⊗[ℂ] B) :=
  Submodule.span ℂ {z | ∃ a c, c ∈ J ∧ z = a ⊗ₜ[ℂ] c}

omit [Nontrivial A] [Nontrivial B] in
theorem tmul_mem_algIdealTensorSpanRight {J : Submodule ℂ B} (a : A) {c : B}
    (hc : c ∈ J) : (a ⊗ₜ[ℂ] c : A ⊗[ℂ] B) ∈ algIdealTensorSpanRight A J :=
  Submodule.subset_span ⟨a, c, hc, rfl⟩

omit [Nontrivial A] [Nontrivial B] in
/-- **The free half of Fubini, algebraically.**  Every slice of an element of
`A ⊙ J` lies in `J`, for any functional whatever: on a generator the slice is
`φ a • c`, and a submodule is closed under scalars. -/
theorem sliceRight_mem_of_mem_algIdealTensorSpanRight {J : Submodule ℂ B}
    (φ : A →ₗ[ℂ] ℂ) {z : A ⊗[ℂ] B} (hz : z ∈ algIdealTensorSpanRight A J) :
    sliceRight φ z ∈ J := by
  refine Submodule.span_induction (p := fun w _ ↦ sliceRight φ w ∈ J)
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨a, c, hc, rfl⟩
    rw [sliceRight_tmul]
    exact J.smul_mem _ hc
  · rw [map_zero]
    exact J.zero_mem
  · intro w w' _ _ hw hw'
    rw [map_add]
    exact J.add_mem hw hw'
  · intro a w _ hw
    rw [map_smul]
    exact J.smul_mem _ hw

/-- **The free half of Fubini, at the completion.**  If `J` is closed then
every slice of an element of the closed span of `A ⊙ J` inside `A ⊗_min B`
still lies in `J`.

This is the statement the `SO.16` argument needs, and it is exactly as strong
as continuity of the slice: the set of elements whose slice lands in `J` is
the preimage of a closed set under a continuous map, hence closed, and it
contains the algebraic span by the previous theorem. -/
theorem sliceRightMin_mem_of_mem_closure (φ : State A) (ξ ξ' : φ.GNSSpace)
    (J : Submodule ℂ B) (hJ : IsClosed (J : Set B))
    {z : MinTensorProduct A B}
    (hz : z ∈ closure (minTensorIn A B ''
      (algIdealTensorSpanRight A J : Set (A ⊗[ℂ] B)))) :
    sliceRightMin φ ξ ξ' z ∈ J := by
  have hclosed : IsClosed {w : MinTensorProduct A B |
      sliceRightMin φ ξ ξ' w ∈ J} :=
    hJ.preimage (sliceRightMin φ ξ ξ').continuous
  have hsub : minTensorIn A B '' (algIdealTensorSpanRight A J : Set (A ⊗[ℂ] B))
      ⊆ {w : MinTensorProduct A B | sliceRightMin φ ξ ξ' w ∈ J} := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using sliceRight_mem_of_mem_algIdealTensorSpanRight _ hx
  exact hclosed.closure_subset_iff.mpr hsub hz

end

end CStarTensor
end GroupApproximation
