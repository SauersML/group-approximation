import GroupApproximation.Analysis.CStarMinTensorQuotient
import GroupApproximation.Analysis.CStarMaxTensorNorm
import GroupApproximation.Meta.AxiomGuard

/-!
# The quotient map on maximal tensor products

## Why this module exists

The manuscript's nonnuclearity sentence for `C^*_{\max}(W)`
(`non_mf_groups_exist.tex`, line 271) needs one permanence property:
*quotients of nuclear C⋆-algebras are nuclear*.  At the completely positive
approximation property that is the Choi--Effros theorem and is out of reach;
at the tensor definition `‖·‖_min = ‖·‖_max` it follows from **maximal
exactness**,

> `(B ⧸ I) ⊗_max C = (B ⊗_max C) / closure(I ⊙ C)`,

together with `nuclear ⟹ exact`.  This module builds the map that statement is
about, and proves the inclusion of the kernel that holds without any
hypothesis.  `Analysis/CStarMinTensorQuotient` is the same construction on the
minimal side and this file is written to mirror it declaration for
declaration.

## The asymmetry worth recording

On the minimal side, contractivity of `q ⊗ id` is a real theorem: it is the
state-pullback argument of `CStarMinTensorFunctorial`, it needs GNS
comparison isometries, and it needs `q` to be **surjective**.

On the maximal side it is three lines and needs no surjectivity at all.  The
maximal norm is a supremum over the *set* of C⋆-seminorms contractive on both
factors, and the pullback of such a seminorm along `q ⊗ id` is again one of
them — a C⋆-seminorm because `q ⊗ id` is a ⋆-homomorphism, contractive on the
left factor because `q` is contractive, and on the right factor because `q` is
unital.  So `maxTensorNorm ((q ⊗ id) x) ≤ maxTensorNorm x` is one application
of `le_maxTensorNorm`.

That is the general pattern: the maximal norm is easy to map *out of* and hard
to compute, the minimal norm is easy to compute and hard to map out of.

## What is here and what is not

Here: the pullback of a C⋆-seminorm along a ⋆-homomorphism, the functoriality
inequality, the induced map `B ⊗_max C → (B ⧸ I) ⊗_max C`, and the inclusion
`closure(I ⊙ C) ⊆ ker`.

Not here: the reverse inclusion, which is maximal exactness proper.  Its proof
is a universal-property argument and every ingredient it needs is now in the
tree — `maxTensorProduct_existsUnique_lift` for the universal property of the
maximal tensor product, `CStarQuotientHom.quotientStarLift` for the universal
property of a C⋆-quotient, and the unconditional C⋆-algebra structure on a
quotient from `Analysis/CStarIdealApproximateUnit`.  What it costs is the
bookkeeping of exhibiting `closure(I ⊙ C)` as a closed, two-sided, star-stable
ideal of `B ⊗_max C` so that the quotient by it is a C⋆-algebra; that is
deliberately left to a lane that can carry it, and nothing here pretends it is
done.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace CStarTensor

open scoped TensorProduct

universe u v w

/-! ## Pullback of a C⋆-seminorm along a ⋆-homomorphism -/

/-- A C⋆-seminorm pulled back along a ⋆-algebra homomorphism is again a
C⋆-seminorm.  Every clause is the corresponding clause for `p` at the image,
because `f` preserves addition, scalars, multiplication and the involution. -/
theorem isCStarSeminorm_comp_starAlgHom
    {A : Type u} {B : Type v} [Ring A] [StarRing A] [Algebra ℂ A]
    [Ring B] [StarRing B] [Algebra ℂ B] {p : B → ℝ}
    (hp : IsCStarSeminorm p) (f : A →⋆ₐ[ℂ] B) :
    IsCStarSeminorm fun a : A ↦ p (f a) where
  nonneg a := hp.nonneg _
  add_le a b := by
    simpa only [map_add] using hp.add_le (f a) (f b)
  smul c a := by
    simpa only [map_smul] using hp.smul c (f a)
  mul_le a b := by
    simpa only [map_mul] using hp.mul_le (f a) (f b)
  cstar a := by
    simpa only [map_mul, map_star] using hp.cstar (f a)

/-! ## Functoriality of the maximal tensor norm -/

section Functorial

variable {B : Type u} {Q : Type v} {C : Type w}
  [CStarAlgebra B] [CStarAlgebra Q] [CStarAlgebra C]
  [Nontrivial B] [Nontrivial Q] [Nontrivial C]

omit [Nontrivial B] in
/-- **The maximal tensor norm is functorial**: `q ⊗ id` is contractive for the
maximal norms, for **every** unital ⋆-homomorphism `q`, surjective or not.

The pullback of the maximal norm of `Q ⊙ C` along `q ⊗ id` is a C⋆-seminorm on
`B ⊙ C` contractive on both factors, so it is dominated by the maximal norm
there. -/
theorem maxTensorNorm_map_le (q : B →⋆ₐ[ℂ] Q) (x : B ⊗[ℂ] C) :
    maxTensorNorm (tensorStarAlgHomMap q x) ≤ maxTensorNorm x := by
  have hpull : IsTensorCStarSeminorm
      fun y : B ⊗[ℂ] C ↦ maxTensorNorm (tensorStarAlgHomMap (C := C) q y) := by
    refine ⟨isCStarSeminorm_comp_starAlgHom isCStarSeminorm_maxTensorNorm _,
      ?_, ?_⟩
    · intro b
      show maxTensorNorm (tensorStarAlgHomMap (C := C) q (b ⊗ₜ[ℂ] (1 : C)))
        ≤ ‖b‖
      rw [tensorStarAlgHomMap_apply, Algebra.TensorProduct.map_tmul]
      show maxTensorNorm ((q b) ⊗ₜ[ℂ] (AlgHom.id ℂ C) 1) ≤ ‖b‖
      rw [map_one, maxTensorNorm_tmul, CStarRing.norm_one, mul_one]
      exact NonUnitalStarAlgHom.norm_apply_le q b
    · intro c
      show maxTensorNorm (tensorStarAlgHomMap (C := C) q ((1 : B) ⊗ₜ[ℂ] c))
        ≤ ‖c‖
      rw [tensorStarAlgHomMap_apply, Algebra.TensorProduct.map_tmul]
      show maxTensorNorm ((q 1) ⊗ₜ[ℂ] (AlgHom.id ℂ C) c) ≤ ‖c‖
      rw [map_one]
      show maxTensorNorm ((1 : Q) ⊗ₜ[ℂ] c) ≤ ‖c‖
      rw [maxTensorNorm_tmul, CStarRing.norm_one, one_mul]
  exact le_maxTensorNorm hpull x

end Functorial

/-! ## The quotient map -/

section QuotientMap

variable {B : Type u} {C : Type w} [CStarAlgebra B] [CStarAlgebra C]
  [Nontrivial B] [Nontrivial C]
  (I : Ideal B) [I.IsTwoSided] [IsStarStable I] [IsClosed (I : Set B)]
  [Nontrivial (B ⧸ I)]

/-- The pre-completion quotient tensor map: unretag, apply `q ⊗ id`, land in
the completed target. -/
noncomputable def maxPreQuotientMap :
    (MaxPreTensor B C) →⋆ₐ[ℂ] MaxTensorProduct (B ⧸ I) C :=
  ((maxTensorIn (B ⧸ I) C).comp
    (tensorStarAlgHomMap (quotientStarMk I))).comp
    (WithCStarNorm.unretagStarAlgHom isCStarNorm_maxTensorNorm)

/-- The pre-completion map is contractive, by `maxTensorNorm_map_le`. -/
theorem norm_maxPreQuotientMap_le (x : MaxPreTensor B C) :
    ‖maxPreQuotientMap (C := C) I x‖ ≤ ‖x‖ := by
  show ‖maxTensorIn (B ⧸ I) C
      (tensorStarAlgHomMap (quotientStarMk I)
        (WithCStarNorm.unretagStarAlgHom isCStarNorm_maxTensorNorm x))‖
    ≤ ‖x‖
  rw [norm_maxTensorIn]
  exact maxTensorNorm_map_le (quotientStarMk I) _

/-- **The quotient map on maximal tensor products**: the contractive extension
of `q ⊗ id` across the completion. -/
noncomputable def quotientMaxTensorMap :
    MaxTensorProduct B C →⋆ₐ[ℂ] MaxTensorProduct (B ⧸ I) C :=
  CStarCompletion.extendStarAlgHom (maxPreQuotientMap (C := C) I)
    (CStarCompletion.uniformContinuous_of_norm_le _
      (norm_maxPreQuotientMap_le (C := C) I))

/-- On the algebraic tensor product the quotient map is `q ⊗ id`. -/
theorem quotientMaxTensorMap_maxTensorIn (x : B ⊗[ℂ] C) :
    quotientMaxTensorMap (C := C) I (maxTensorIn B C x)
      = maxTensorIn (B ⧸ I) C
          (tensorStarAlgHomMap (quotientStarMk I) x) := by
  show CStarCompletion.extendStarAlgHom _ _ (maxTensorIn B C x) = _
  exact CStarCompletion.extendStarAlgHom_coe _ _ _

/-! ## The provable inclusion -/

/-- The span of the image of `I ⊙ C` inside `B ⊗_max C`. -/
noncomputable def idealMaxTensorSpan : Submodule ℂ (MaxTensorProduct B C) :=
  Submodule.span ℂ
    {z | ∃ b c, b ∈ I ∧ z = maxTensorIn B C (b ⊗ₜ[ℂ] c)}

/-- **The closure of `I ⊙ C` lies in the kernel of the quotient map.**  On a
generator `b ⊗ₜ c` with `b ∈ I` the image is `0 ⊗ₜ c = 0`, the kernel is a
closed submodule, and the closure of a span inside a kernel stays inside. -/
theorem idealMaxTensorSpan_subset_ker (z : MaxTensorProduct B C)
    (hz : z ∈ closure
      (idealMaxTensorSpan (C := C) I : Set (MaxTensorProduct B C))) :
    quotientMaxTensorMap (C := C) I z = 0 := by
  have hgen : ∀ w ∈ (idealMaxTensorSpan (C := C) I :
      Set (MaxTensorProduct B C)), quotientMaxTensorMap (C := C) I w = 0 := by
    intro w hw
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨b, c, hb, rfl⟩
      rw [quotientMaxTensorMap_maxTensorIn, tensorStarAlgHomMap_apply,
        Algebra.TensorProduct.map_tmul]
      have hb0 : quotientStarMk I b = 0 := by
        rw [quotientStarMk_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact hb
      show maxTensorIn (B ⧸ I) C ((quotientStarMk I b) ⊗ₜ[ℂ] c) = 0
      rw [hb0, TensorProduct.zero_tmul, map_zero]
    · rw [map_zero]
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro a x _ hx
      rw [map_smul, hx, smul_zero]
  have hcont : Continuous (quotientMaxTensorMap (C := C) I) :=
    UniformSpace.Completion.continuous_extension
      (f := ((maxPreQuotientMap (C := C) I :
          MaxPreTensor B C →⋆ₐ[ℂ] MaxTensorProduct (B ⧸ I) C) :
        MaxPreTensor B C → MaxTensorProduct (B ⧸ I) C))
  have hclosed : IsClosed {w : MaxTensorProduct B C |
      quotientMaxTensorMap (C := C) I w = 0} :=
    isClosed_eq hcont continuous_const
  exact hclosed.closure_subset_iff.mpr hgen hz

/-! ## Maximal exactness, as a statement

The reverse inclusion is what "maximal exactness" means.  It is stated here as
a proposition about the pair `(B, I)` and a test algebra so that the residual
is a type rather than a remark, and it is **not proved**. -/

/-- **Maximal exactness for one pair and one test algebra**: the kernel of
`q ⊗_max id` is no larger than the closure of `I ⊙ C`.

Classically this is a universal-property argument, and it is *not* the
delicate half of tensor theory — the delicate half is the same statement for
`⊗_min`, which is exactness of `C` and is false in general.  It is left
unproved here only because exhibiting `closure(I ⊙ C)` as a closed two-sided
star-stable ideal of `B ⊗_max C`, so that the quotient by it is a C⋆-algebra
with a universal property to compare against, is bookkeeping this module does
not carry. -/
def IsMaxExactAt : Prop :=
  ∀ z : MaxTensorProduct B C, quotientMaxTensorMap (C := C) I z = 0 →
    z ∈ closure
      (idealMaxTensorSpan (C := C) I : Set (MaxTensorProduct B C))

end QuotientMap

end CStarTensor
end GroupApproximation

open GroupApproximation.CStarTensor

#audit_axioms GroupApproximation.CStarTensor.maxTensorNorm_map_le

#audit_axioms GroupApproximation.CStarTensor.idealMaxTensorSpan_subset_ker
