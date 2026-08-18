import GroupApproximation.Analysis.CStarMaxTensorNorm
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# The comparison map `A ⊗_max B → A ⊗_min B`

## What this module builds

`CStarMaxTensorNorm` proves `minTensorNorm ≤ maxTensorNorm`.  That single
inequality says the identity of the algebraic tensor product is norm-decreasing
from the maximal norm to the minimal one, so it extends across the completion:

* `maxToMin` — the canonical ⋆-homomorphism `A ⊗_max B → A ⊗_min B`, the
  identity on elementary tensors (`maxToMin_maxTensorIn`);
* `norm_maxToMin_le` — it is contractive;
* `denseRange_maxToMin` — its range is dense, because it already contains the
  image of the algebraic tensor product;
* `maxToMin_injective_iff` — **the kernel statement**: the comparison map is
  injective exactly when the two norms agree on the algebraic tensor product.

The last of these is the reason the map is worth building.  It says the kernel
of `maxToMin` is precisely the obstruction measured by `‖·‖_min < ‖·‖_max`, so
a nuclearity-style hypothesis ("the two norms agree") and a structural one
("the comparison map is injective") are the same hypothesis, and a proof may
use whichever is convenient.

## Why the equivalence needs a theorem in each direction

Neither direction is formal.

*If the norms agree*, the two continuous functions `z ↦ ‖maxToMin z‖` and
`z ↦ ‖z‖` agree on the image of `A ⊙ B`, which is dense, so they agree
everywhere and `maxToMin` is isometric, hence injective.  This uses only
density and continuity.

*If the map is injective*, it is **isometric** — and that is not formal at all:
it is the theorem that an injective ⋆-homomorphism of complex C⋆-algebras
preserves norms (`NonUnitalStarAlgHom.norm_map`, whose proof runs through the
unitization and the spectral radius of a selfadjoint element).  Reading it at
an elementary tensor's image then returns the equality of the two norms.

## What is *not* claimed: surjectivity

The range is dense and is not shown to be everything.  The classical statement
is that `maxToMin` is a surjection, and the classical proof is that a
⋆-homomorphism of C⋆-algebras has closed range: factor through
`A ⊗_max B ⧸ ker`, observe the induced map is injective, hence isometric by
the theorem just quoted, hence its range is complete and so closed; a dense
closed set is everything.

Every ingredient of that argument now exists in this development —
`CStarIdealQuotient` and `CStarIdealApproximateUnit` make the quotient of a
C⋆-algebra by a closed star-stable two-sided ideal a C⋆-algebra, and the
isometry theorem is Mathlib's — but the argument is not carried out here, so
no declaration below is named `surjective` and none claims it.  What is
available is `denseRange_maxToMin`, and it is stated as density because that is
what is proved.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `SO.16` and `RE.05`
remain **MISSING**.
-/

namespace GroupApproximation
namespace CStarTensor

open scoped TensorProduct CStarAlgebra

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
  [Nontrivial A] [Nontrivial B]

/-! ## The map -/

/-- The comparison map on the pre-C⋆-algebra: the identity of `A ⊙ B`, read out
of the maximal norm and into the minimal completion.  It is contractive by
`minTensorNorm_le_maxTensorNorm`, which is the whole content. -/
noncomputable def maxToMinPre :
    MaxPreTensor A B →⋆ₐ[ℂ] MinTensorProduct A B :=
  (minTensorIn A B).comp
    (WithCStarNorm.unretagStarAlgHom isCStarNorm_maxTensorNorm)

theorem norm_maxToMinPre_le (y : MaxPreTensor A B) : ‖maxToMinPre y‖ ≤ ‖y‖ := by
  show ‖minTensorIn A B y‖ ≤ maxTensorNorm y
  rw [norm_minTensorIn]
  exact minTensorNorm_le_maxTensorNorm y

/-- **The comparison map `A ⊗_max B → A ⊗_min B`.**  The identity of the
algebraic tensor product, extended across the completion; it exists because the
minimal norm is dominated by the maximal one. -/
noncomputable def maxToMin :
    MaxTensorProduct A B →⋆ₐ[ℂ] MinTensorProduct A B :=
  CStarCompletion.extendStarAlgHom maxToMinPre
    (CStarCompletion.uniformContinuous_of_norm_le _ norm_maxToMinPre_le)

/-- The comparison map is the identity on the algebraic tensor product: it
carries the copy of `A ⊙ B` inside `A ⊗_max B` onto the copy inside
`A ⊗_min B`. -/
@[simp] theorem maxToMin_maxTensorIn (x : A ⊗[ℂ] B) :
    maxToMin (maxTensorIn A B x) = minTensorIn A B x :=
  CStarCompletion.extendStarAlgHom_coe maxToMinPre
    (CStarCompletion.uniformContinuous_of_norm_le _ norm_maxToMinPre_le)
    (WithCStarNorm.retagStarAlgHom isCStarNorm_maxTensorNorm x)

/-- On an elementary tensor the comparison map does nothing but change which
norm the ambient algebra carries. -/
theorem maxToMin_tmul (a : A) (b : B) :
    maxToMin (maxTensorIn A B (a ⊗ₜ[ℂ] b)) = minTensorIn A B (a ⊗ₜ[ℂ] b) :=
  maxToMin_maxTensorIn _

/-- **The comparison map is contractive**, as every ⋆-homomorphism of
C⋆-algebras is. -/
theorem norm_maxToMin_le (z : MaxTensorProduct A B) : ‖maxToMin z‖ ≤ ‖z‖ :=
  NonUnitalStarAlgHom.norm_apply_le maxToMin z

/-- **The range of the comparison map is dense**: it already contains the image
of the algebraic tensor product, which is dense in `A ⊗_min B`.

This is density, not surjectivity; see the module docstring for what closing
that gap would take. -/
theorem denseRange_maxToMin : DenseRange (maxToMin (A := A) (B := B)) := by
  refine Dense.mono ?_ denseRange_minTensorIn
  rintro _ ⟨x, rfl⟩
  exact ⟨maxTensorIn A B x, maxToMin_maxTensorIn x⟩

/-! ## The kernel -/

/-- If the two norms agree on the algebraic tensor product then the comparison
map is **isometric**: the two continuous functions `‖maxToMin ·‖` and `‖·‖`
agree on a dense set. -/
theorem norm_maxToMin_of_norm_eq
    (hnorm : ∀ x : A ⊗[ℂ] B, maxTensorNorm x = minTensorNorm x)
    (z : MaxTensorProduct A B) : ‖maxToMin z‖ = ‖z‖ := by
  have hagree : (fun w : MaxTensorProduct A B ↦ ‖maxToMin w‖) ∘ (maxTensorIn A B)
      = (fun w : MaxTensorProduct A B ↦ ‖w‖) ∘ (maxTensorIn A B) := by
    funext x
    show ‖maxToMin (maxTensorIn A B x)‖ = ‖maxTensorIn A B x‖
    rw [maxToMin_maxTensorIn, norm_minTensorIn, norm_maxTensorIn, hnorm x]
  have := denseRange_maxTensorIn.equalizer
    (continuous_norm.comp (continuous_of_maxTensorProduct maxToMin))
    continuous_norm hagree
  exact congrFun this z

/-- **The kernel statement.**  The comparison map is injective exactly when the
maximal and minimal norms agree on the algebraic tensor product.

The forward direction is the theorem that an injective ⋆-homomorphism of
complex C⋆-algebras is isometric; the reverse is density and continuity. -/
theorem maxToMin_injective_iff :
    Function.Injective (maxToMin (A := A) (B := B))
      ↔ ∀ x : A ⊗[ℂ] B, maxTensorNorm x = minTensorNorm x := by
  constructor
  · intro hinj x
    have h := NonUnitalStarAlgHom.norm_map maxToMin hinj (maxTensorIn A B x)
    rw [maxToMin_maxTensorIn, norm_minTensorIn, norm_maxTensorIn] at h
    exact h.symm
  · intro hnorm z w hzw
    have hz : ‖z - w‖ = 0 := by
      rw [← norm_maxToMin_of_norm_eq hnorm (z - w), map_sub, hzw, sub_self,
        norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- The two norms agree exactly when the comparison map is injective, stated in
the direction a nuclearity-style hypothesis is usually met in. -/
theorem norm_eq_iff_maxToMin_injective :
    (∀ x : A ⊗[ℂ] B, maxTensorNorm x = minTensorNorm x)
      ↔ Function.Injective (maxToMin (A := A) (B := B)) :=
  maxToMin_injective_iff.symm

end CStarTensor
end GroupApproximation
