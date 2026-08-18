import GroupApproximation.Analysis.CStarMinTensorFunctorial
import GroupApproximation.Analysis.CStarIdealApproximateUnit

/-!
# The quotient map on minimal tensor products, and exactness as a statement

## What this module builds

For a closed star-stable two-sided ideal `I` of a unital C⋆-algebra `B`
(with nontrivial quotient) and any unital C⋆-algebra `C`:

* `tensorStarAlgHomMap` -- `q ⊗ id` on algebraic tensors as a
  ⋆-homomorphism, for any unital ⋆-homomorphism `q`;
* `quotientMinTensorMap` -- the induced ⋆-homomorphism
  `B ⊗_min C → (B ⧸ I) ⊗_min C`, obtained from the contractivity of
  `q ⊗ id` for surjective `q` (`minTensorNorm_map_le`) and the extension of
  bounded ⋆-homomorphisms across completions;
* `idealTensorSpan` and `idealTensorSpan_subset_ker` -- the closure of
  `I ⊙ C` inside `B ⊗_min C` lies in the kernel of the quotient map: the
  provable inclusion of the exactness sequence;
* `IsExactCStar` -- **the exactness predicate, statable at last**: `C` is
  exact when for every such `(B, I)` the kernel of the quotient map is
  exactly the closure of `I ⊙ C`.

## What is claimed and what is not

The definition is the textbook kernel form of exactness of the sequence
`0 → I ⊗ C → B ⊗ C → (B ⧸ I) ⊗ C → 0` at the middle, phrased against the
canonical `⊗_min` of `CStarMinTensorNorm`.  The inclusion
`closure (I ⊙ C) ⊆ ker` is proved here; the reverse inclusion for
particular `C` is the mathematical content of exactness and is proved for
no algebra in this development.  The left leg -- that `I ⊗_min C` embeds
isometrically -- is a separate open statement (Takesaki-adjacent) and is
deliberately not folded into the predicate: the kernel form quantifies only
over objects this development constructs canonically.

The standing record in `CStarExactness.lean` said exactness was
**unstatable** for want of `⊗_min` and the C⋆-quotient.  Both now exist,
and this definition discharges exactly that statability debt; the
manuscript's row remains **MISSING** because no theorem here proves any
algebra exact.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `SO.16` and
`RE.05` remain **MISSING**.
-/

namespace GroupApproximation
namespace CStarTensor

open CStarState
open scoped TensorProduct

universe u v w

section TensorMap

variable {B : Type u} {Q : Type v} {C : Type w}
  [CStarAlgebra B] [CStarAlgebra Q] [CStarAlgebra C]

/-- `q ⊗ id` on algebraic tensors, as a ⋆-homomorphism. -/
noncomputable def tensorStarAlgHomMap (q : B →⋆ₐ[ℂ] Q) :
    (B ⊗[ℂ] C) →⋆ₐ[ℂ] (Q ⊗[ℂ] C) :=
  { Algebra.TensorProduct.map q.toAlgHom (AlgHom.id ℂ C) with
    map_star' := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b c =>
          show Algebra.TensorProduct.map q.toAlgHom (AlgHom.id ℂ C)
              (star (b ⊗ₜ[ℂ] c))
            = star (Algebra.TensorProduct.map q.toAlgHom (AlgHom.id ℂ C)
                (b ⊗ₜ[ℂ] c))
          rw [TensorProduct.star_tmul, Algebra.TensorProduct.map_tmul,
            Algebra.TensorProduct.map_tmul, TensorProduct.star_tmul,
            map_star]
          rfl
      | add y z hy hz =>
          show Algebra.TensorProduct.map q.toAlgHom (AlgHom.id ℂ C)
              (star (y + z)) = _
          rw [star_add, map_add]
          rw [show Algebra.TensorProduct.map q.toAlgHom (AlgHom.id ℂ C)
              (star y) = _ from hy,
            show Algebra.TensorProduct.map q.toAlgHom (AlgHom.id ℂ C)
              (star z) = _ from hz]
          rw [map_add, star_add] }

@[simp] theorem tensorStarAlgHomMap_apply (q : B →⋆ₐ[ℂ] Q) (x : B ⊗[ℂ] C) :
    tensorStarAlgHomMap q x
      = Algebra.TensorProduct.map q.toAlgHom (AlgHom.id ℂ C) x := rfl

end TensorMap

section QuotientMap

variable {B : Type u} {C : Type w} [CStarAlgebra B] [CStarAlgebra C]
  [Nontrivial B] [Nontrivial C]
  (I : Ideal B) [I.IsTwoSided] [IsStarStable I] [IsClosed (I : Set B)]
  [Nontrivial (B ⧸ I)]

/-- The quotient ⋆-homomorphism is surjective. -/
theorem quotientStarMk_surjective :
    Function.Surjective (quotientStarMk I) := by
  intro x
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨b, by rw [quotientStarMk_apply, hb]⟩

/-- The pre-completion quotient tensor map: unretag, apply `q ⊗ id`, land in
the completed target. -/
noncomputable def minPreQuotientMap :
    (MinPreTensor B C) →⋆ₐ[ℂ] MinTensorProduct (B ⧸ I) C :=
  ((minTensorIn (B ⧸ I) C).comp
    (tensorStarAlgHomMap (quotientStarMk I))).comp
    (WithCStarNorm.unretagStarAlgHom isCStarNorm_minTensorNorm)

/-- The pre-completion map is contractive: the functoriality inequality for
the surjective quotient homomorphism. -/
theorem norm_minPreQuotientMap_le (x : MinPreTensor B C) :
    ‖minPreQuotientMap I x‖ ≤ ‖x‖ := by
  show ‖minTensorIn (B ⧸ I) C
      (tensorStarAlgHomMap (quotientStarMk I)
        (WithCStarNorm.unretagStarAlgHom isCStarNorm_minTensorNorm x))‖
    ≤ ‖x‖
  rw [norm_minTensorIn, tensorStarAlgHomMap_apply]
  exact minTensorNorm_map_le (quotientStarMk I)
    (quotientStarMk_surjective I) _

/-- **The quotient map on minimal tensor products**: the contractive
extension of `q ⊗ id` across the completion. -/
noncomputable def quotientMinTensorMap :
    MinTensorProduct B C →⋆ₐ[ℂ] MinTensorProduct (B ⧸ I) C :=
  CStarCompletion.extendStarAlgHom (minPreQuotientMap I)
    (CStarCompletion.uniformContinuous_of_norm_le _
      (norm_minPreQuotientMap_le I))

/-- On the algebraic tensor product, the quotient map is `q ⊗ id`. -/
theorem quotientMinTensorMap_minTensorIn (x : B ⊗[ℂ] C) :
    quotientMinTensorMap I (minTensorIn B C x)
      = minTensorIn (B ⧸ I) C
          (tensorStarAlgHomMap (quotientStarMk I) x) := by
  show CStarCompletion.extendStarAlgHom _ _
      (minTensorIn B C x) = _
  exact CStarCompletion.extendStarAlgHom_coe _ _ _

/-! ## The provable inclusion -/

/-- The span of the image of `I ⊙ C` inside `B ⊗_min C`. -/
def idealTensorSpan : Submodule ℂ (MinTensorProduct B C) :=
  Submodule.span ℂ
    {z | ∃ b c, b ∈ I ∧ z = minTensorIn B C (b ⊗ₜ[ℂ] c)}

/-- **The closure of `I ⊙ C` lies in the kernel of the quotient map**: on a
generator `b ⊗ₜ c` with `b ∈ I` the image is `mk b ⊗ₜ c = 0 ⊗ₜ c = 0`, the
kernel is a closed submodule, and closures of spans of subsets of kernels
stay inside. -/
theorem idealTensorSpan_subset_ker (z : MinTensorProduct B C)
    (hz : z ∈ closure (idealTensorSpan (C := C) I : Set (MinTensorProduct B C))) :
    quotientMinTensorMap I z = 0 := by
  have hgen : ∀ w ∈ (idealTensorSpan (C := C) I :
      Set (MinTensorProduct B C)), quotientMinTensorMap I w = 0 := by
    intro w hw
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨b, c, hb, rfl⟩
      rw [quotientMinTensorMap_minTensorIn, tensorStarAlgHomMap_apply,
        Algebra.TensorProduct.map_tmul]
      have hb0 : quotientStarMk I b = 0 := by
        rw [quotientStarMk_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact hb
      show minTensorIn (B ⧸ I) C ((quotientStarMk I b) ⊗ₜ[ℂ] c) = 0
      rw [hb0, TensorProduct.zero_tmul, map_zero]
    · rw [map_zero]
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro a x _ hx
      rw [map_smul, hx, smul_zero]
  -- Pass to the closure by continuity.
  have hcont : Continuous (quotientMinTensorMap I) := by
    have := CStarCompletion.uniformContinuous_of_norm_le
      (minPreQuotientMap I) (norm_minPreQuotientMap_le I)
    exact UniformSpace.Completion.continuous_extension
  have hclosed : IsClosed {w : MinTensorProduct B C |
      quotientMinTensorMap I w = 0} :=
    isClosed_eq hcont continuous_const
  exact hclosed.closure_subset_iff.mpr hgen hz

end QuotientMap

/-! ## Exactness, statable -/

variable (C : Type w) [CStarAlgebra C] [Nontrivial C]

/-- **Exactness of a C⋆-algebra**, in the kernel form of the textbook
definition against the canonical minimal tensor product: for every closed
star-stable two-sided ideal of every unital C⋆-algebra with nontrivial
quotient, the kernel of the induced quotient map on `⊗_min` is exactly the
closure of `I ⊙ C`.

One inclusion holds always (`idealTensorSpan_subset_ker`); the predicate
asserts the other.  No theorem in this development proves any algebra
exact; the definition exists so that the manuscript's exactness sentence
is *statable*, which the standing record in `CStarExactness.lean` recorded
as the vocabulary gap. -/
def IsExactCStar : Prop :=
  ∀ (B : Type u) (_ : CStarAlgebra B) (_ : Nontrivial B) (I : Ideal B)
    (_ : I.IsTwoSided) (_ : IsStarStable I) (_ : IsClosed (I : Set B))
    (_ : Nontrivial (B ⧸ I)) (z : MinTensorProduct B C),
      quotientMinTensorMap I z = 0 →
        z ∈ closure (idealTensorSpan (C := C) I :
          Set (MinTensorProduct B C))

end CStarTensor
end GroupApproximation
