import GroupApproximation.Analysis.CStarSliceLeft
import GroupApproximation.Analysis.CStarMinTensorQuotient

/-!
# Exactness follows from the slice map property

Proof-ledger row `SO.16`.  The manuscript prints that `C*_red(E)` is exact,
and `CStarMinTensorQuotient` made that statable: `IsExactCStar C` says that
for every closed star-stable two-sided ideal `I ◁ B`, the kernel of
`B ⊗_min C → (B ⧸ I) ⊗_min C` is exactly the closed span of `I ⊙ C`.  One
inclusion is proved there; the other is the content, and no algebra in this
development is exact.

This module does not prove any algebra exact either.  It replaces the
unproved inclusion by a statement about slices, which is what the printed
argument actually uses, and proves the half of that replacement that is
unconditional.

## The sandwich

For a state `ψ` of `C` and vectors `η, η'` of its GNS space, `sliceLeftMin`
is the continuous second-variable slice `B ⊗_min C → B` of
`Analysis/CStarSliceLeft`.  Three sets are then in play:

`closure (I ⊙ C)` ⊆ `ker (q ⊗ id)` ⊆ `{z | every slice of z lies in I}`.

The first inclusion is `idealTensorSpan_subset_ker`.  The second is
`sliceLeftMin_mem_of_quotientMinTensorMap_eq_zero`, proved here: slices
commute with `q ⊗ id`, so a `z` killed by the quotient map has every slice
killed by `q`, and the kernel of `q` is `I`.

Exactness asks for the outer two to coincide.  So it suffices --- and this is
`isExactCStar_of_hasSliceMapProperty` --- that the *third* set be contained in
the first: an element all of whose slices lie in the ideal lies in the closed
span.  That is the slice map property, and it is the honest name for what the
exactness sentence needs.

## What is still open

The slice map property is false for general C⋆-algebras and is proved here for
none.  `SO.16` does not move.  What moves is the shape of the debt: it was
"prove exactness", stated against a tensor-product kernel, and it is now
"prove the slice map property", stated against slices of individual elements,
which is the form the literature argument takes and the form a future proof
can be attacked in.

## Manuscript status

Reduces the unproved half of `SO.16` to a named property; certifies no
manuscript step.
-/

namespace GroupApproximation
namespace CStarTensor

open CStarState
open scoped TensorProduct

universe u v w

noncomputable section

/-! ## Slices commute with a ⋆-homomorphism on the left leg -/

section Algebraic

variable {B : Type u} {Q : Type v} {C : Type w}
  [CStarAlgebra B] [CStarAlgebra Q] [CStarAlgebra C]

/-- **Naturality of the second-variable slice**, algebraically: slicing after
`q ⊗ id` is `q` after slicing.  On `a ⊗ b` both sides are `ψ b • q a`. -/
theorem sliceLeft_tensorStarAlgHomMap (q : B →⋆ₐ[ℂ] Q) (ψ : C →ₗ[ℂ] ℂ)
    (x : B ⊗[ℂ] C) :
    sliceLeft ψ (tensorStarAlgHomMap (C := C) q x) = q (sliceLeft ψ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      rw [tensorStarAlgHomMap_apply, Algebra.TensorProduct.map_tmul]
      show sliceLeft ψ ((q a) ⊗ₜ[ℂ] b) = q (sliceLeft ψ (a ⊗ₜ[ℂ] b))
      rw [sliceLeft_tmul, sliceLeft_tmul, map_smul]
  | add x y hx hy =>
      simp only [map_add, hx, hy]

end Algebraic

/-! ## The two continuities the density argument needs -/

section Quotient

variable {B : Type u} {C : Type w} [CStarAlgebra B] [CStarAlgebra C]
  [Nontrivial B] [Nontrivial C]
  (I : Ideal B) [I.IsTwoSided] [IsStarStable I] [IsClosed (I : Set B)]
  [Nontrivial (B ⧸ I)]

omit [Nontrivial B] [Nontrivial C] [IsClosed (I : Set B)]
  [Nontrivial (B ⧸ I)] in
/-- The quotient ⋆-homomorphism is contractive, hence continuous. -/
theorem continuous_quotientStarMk : Continuous (quotientStarMk I) := by
  refine AddMonoidHomClass.continuous_of_bound (quotientStarMk I) 1 fun a ↦ ?_
  rw [one_mul, quotientStarMk_apply]
  exact quotient_norm_mk_le I a

/-- The quotient map on minimal tensor products is continuous: it is the
uniform extension of a contractive map across the completion. -/
theorem continuous_quotientMinTensorMap :
    Continuous (quotientMinTensorMap (C := C) I) :=
  UniformSpace.Completion.continuous_extension
    (f := ((minPreQuotientMap I :
        MinPreTensor B C →⋆ₐ[ℂ] MinTensorProduct (B ⧸ I) C) :
      MinPreTensor B C → MinTensorProduct (B ⧸ I) C))

/-! ## Naturality at the completion, and the kernel inclusion -/

/-- **Naturality of the slice on `B ⊗_min C`.**  Both sides are continuous and
agree on the dense algebraic tensor product, where the identity is
`sliceLeft_tensorStarAlgHomMap`. -/
theorem sliceLeftMin_quotientMinTensorMap (ψ : State C) (η η' : ψ.GNSSpace)
    (z : MinTensorProduct B C) :
    sliceLeftMin (A := B ⧸ I) ψ η η' (quotientMinTensorMap I z)
      = quotientStarMk I (sliceLeftMin (A := B) ψ η η' z) := by
  refine (denseRange_minTensorIn (A := B) (B := C)).induction_on z ?_ ?_
  · exact isClosed_eq
      ((sliceLeftMin (A := B ⧸ I) ψ η η').continuous.comp
        (continuous_quotientMinTensorMap I))
      ((continuous_quotientStarMk I).comp
        (sliceLeftMin (A := B) ψ η η').continuous)
  · intro x
    rw [quotientMinTensorMap_minTensorIn, sliceLeftMin_minTensorIn,
      sliceLeftMin_minTensorIn]
    exact sliceLeft_tensorStarAlgHomMap (quotientStarMk I)
      (vecFunctional ψ.gnsRep η η') x

/-- **The kernel lies inside the slice condition.**  If `q ⊗ id` kills `z`
then every slice of `z` is killed by `q`, and the kernel of `q` is `I`.  This
is the second inclusion of the sandwich, and it is unconditional. -/
theorem sliceLeftMin_mem_of_quotientMinTensorMap_eq_zero
    (ψ : State C) (η η' : ψ.GNSSpace) {z : MinTensorProduct B C}
    (hz : quotientMinTensorMap I z = 0) :
    sliceLeftMin (A := B) ψ η η' z ∈ I := by
  have h := sliceLeftMin_quotientMinTensorMap I ψ η η' z
  rw [hz, map_zero] at h
  have h0 : Ideal.Quotient.mk I (sliceLeftMin (A := B) ψ η η' z) = 0 := by
    rw [← quotientStarMk_apply]
    exact h.symm
  exact Ideal.Quotient.eq_zero_iff_mem.mp h0

end Quotient

/-! ## The reduction -/

variable (C : Type w) [CStarAlgebra C] [Nontrivial C]

/-- **The slice map property** for `C`: an element of `B ⊗_min C` all of whose
second-variable slices lie in a closed ideal `I` lies in the closed span of
`I ⊙ C`.

The binders are written exactly as in `IsExactCStar`, so that the two
predicates can be compared without a translation step. -/
def HasSliceMapProperty : Prop :=
  ∀ (B : Type u) (_ : CStarAlgebra B) (_ : Nontrivial B) (I : Ideal B)
    (_ : I.IsTwoSided) (_ : IsStarStable I) (_ : IsClosed (I : Set B))
    (_ : Nontrivial (B ⧸ I)) (z : MinTensorProduct B C),
      (∀ (ψ : State C) (η η' : ψ.GNSSpace),
          sliceLeftMin (A := B) ψ η η' z ∈ I) →
        z ∈ closure (idealTensorSpan (C := C) I :
          Set (MinTensorProduct B C))

/-- **Exactness follows from the slice map property.**  The kernel of the
quotient map is contained in the slice condition unconditionally, so an
algebra whose slice condition forces membership in the closed span is exact.

This is the reduction the `SO.16` argument needs: it converts an unproved
statement about a tensor-product kernel into an unproved statement about
slices of individual elements, and proves everything between the two. -/
theorem isExactCStar_of_hasSliceMapProperty (h : HasSliceMapProperty.{u} C) :
    IsExactCStar.{u} C := by
  intro B instB instNB I instTS instSS instCl instNQ z hz
  exact h B instB instNB I instTS instSS instCl instNQ z
    (fun ψ η η' ↦
      sliceLeftMin_mem_of_quotientMinTensorMap_eq_zero I ψ η η' hz)

end

end CStarTensor
end GroupApproximation
