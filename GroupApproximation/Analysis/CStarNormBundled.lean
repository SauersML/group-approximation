import GroupApproximation.Analysis.CStarSeminormQuotient
import GroupApproximation.Analysis.CStarCompletion

/-!
# From an unbundled C⋆-norm to a C⋆-algebra

## The connective tissue this supplies

The tensor lane produces C⋆-norms *unbundled*, as functions `A → ℝ`:
`StarRep.seminorm` is `fun a ↦ ‖π.hom a‖`, `StarRep.isCStarNorm_of_injective`
says it is an `IsCStarNorm`, and
`IsCStarSeminorm.exists_isCStarNorm_on_quotient` produces one on a quotient
when the representation is not faithful.  Nothing in that chain is a `Norm`
*instance*, so nothing in it can be fed to `Analysis/CStarCompletion`, which
completes a pre-C⋆-algebra --- and a `Norm` instance is what the completion
needs.

This file is the missing step.  `WithCStarNorm h` is the algebra retagged so
that the chosen C⋆-norm is its norm, and it carries every structure of
`CStarAlgebra` except completeness.  Composing with
`CStarCompletion.completionCStarAlgebra` closes the chain:

  `StarRep`  ⟶  `IsCStarSeminorm`  ⟶  (quotient)  `IsCStarNorm`
             ⟶  pre-C⋆-algebra  ⟶  C⋆-algebra.

`completion_isCStarAlgebra` is the last arrow and the point of the file.

## Why a type synonym

The norm has to be *chosen*: an algebra can carry many C⋆-norms (that is the
whole difficulty of the tensor product), so installing one as an instance on
`A` itself would be wrong.  Indexing the synonym by the proof `h` rather than
by `p` alone makes every instance below inferable, since `h` is recoverable
from the type; proof irrelevance means nothing is duplicated.

Mathlib warns that `AddGroupNorm.toNormedAddCommGroup` "creates bad
definitional equalities ... it does not take into account a possibly existing
`UniformSpace` instance".  On a fresh synonym there is no pre-existing
uniformity, and the additive group structure is the ambient one, so the
warning does not bite here.  It is exactly why this is done on a synonym and
not on `A`.

## Manuscript status

Infrastructure only; certifies no manuscript step.  `SO.16` and `RE.05` remain
**MISSING**: what is still absent is Takesaki's independence theorem (Stage C),
which is what would make the resulting C⋆-algebra `A ⊗_min B` rather than
`A ⊗_{π,ρ} B`.
-/

namespace GroupApproximation
namespace CStarTensor

universe u

section Bundled

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A] {p : A → ℝ}

/-- `A`, retagged so that the C⋆-norm `p` is its norm.  Indexed by the proof so
that the instances below are inferable. -/
def WithCStarNorm (_h : IsCStarNorm p) : Type u := A

namespace WithCStarNorm

/-- The tautological bijection with the underlying algebra. -/
def equiv (h : IsCStarNorm p) : A ≃ WithCStarNorm h := Equiv.refl _

instance ring (h : IsCStarNorm p) : Ring (WithCStarNorm h) :=
  inferInstanceAs (Ring A)

instance starRing (h : IsCStarNorm p) : StarRing (WithCStarNorm h) :=
  inferInstanceAs (StarRing A)

instance algebra (h : IsCStarNorm p) : Algebra ℂ (WithCStarNorm h) :=
  inferInstanceAs (Algebra ℂ A)

instance starModule [StarModule ℂ A] (h : IsCStarNorm p) :
    StarModule ℂ (WithCStarNorm h) :=
  inferInstanceAs (StarModule ℂ A)

/-- The chosen C⋆-norm, installed as the norm.  Its additive group is the
ambient one; only the metric and uniformity are new. -/
noncomputable instance normedAddCommGroup (h : IsCStarNorm p) :
    NormedAddCommGroup (WithCStarNorm h) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := p
      map_zero' := h.isCStarSeminorm.map_zero
      add_le' := h.isCStarSeminorm.add_le
      neg' := h.isCStarSeminorm.map_neg
      eq_zero_of_map_eq_zero' := h.eq_zero }

@[simp] theorem norm_eq (h : IsCStarNorm p) (a : WithCStarNorm h) :
    ‖a‖ = p a := rfl

noncomputable instance normedRing (h : IsCStarNorm p) :
    NormedRing (WithCStarNorm h) :=
  { normedAddCommGroup h, ring h with
    norm_mul_le := h.isCStarSeminorm.mul_le }

/-- The involution is isometric, because a C⋆-seminorm is star-invariant --- a
theorem of `CStarTensorProductSeminorm`, not an axiom. -/
noncomputable instance normedStarGroup (h : IsCStarNorm p) :
    NormedStarGroup (WithCStarNorm h) where
  norm_star_le a := le_of_eq (h.isCStarSeminorm.map_star a)

/-- **The C⋆-identity**, transported from the unbundled statement. -/
noncomputable instance cstarRing (h : IsCStarNorm p) :
    CStarRing (WithCStarNorm h) where
  norm_mul_self_le a := le_of_eq (h.isCStarSeminorm.cstar a).symm

noncomputable instance normedSpace (h : IsCStarNorm p) :
    NormedSpace ℂ (WithCStarNorm h) where
  norm_smul_le c a := le_of_eq (h.isCStarSeminorm.smul c a)

noncomputable instance normedAlgebra (h : IsCStarNorm p) :
    NormedAlgebra ℂ (WithCStarNorm h) where
  norm_smul_le c a := le_of_eq (h.isCStarSeminorm.smul c a)

/-! ### Crossing the retagging

The synonym is `A` itself, so the identity is a ⋆-algebra homomorphism in each
direction and every field is `rfl`.  Both directions live here, beside the
`WithCStarNorm` they retag: the forward arrow was born in
`Analysis/CStarTensorProductAlgebra` and moved here in one commit so that no
call site had to change and no window existed in which the name was declared
twice. -/

/-- The identity of the underlying algebra, as a ⋆-algebra homomorphism into
the retagged copy.  Every field is `rfl` because `WithCStarNorm h` carries the
algebra structure of `A` verbatim; only the norm is new. -/
def retagStarAlgHom (h : IsCStarNorm p) : A →⋆ₐ[ℂ] WithCStarNorm h where
  toFun a := equiv h a
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp] theorem retagStarAlgHom_apply (h : IsCStarNorm p) (a : A) :
    retagStarAlgHom h a = equiv h a := rfl

theorem retagStarAlgHom_surjective (h : IsCStarNorm p) :
    Function.Surjective (retagStarAlgHom h) :=
  fun x => ⟨(equiv h).symm x, rfl⟩

/-- The retagging homomorphism realises the C⋆-norm as the norm. -/
@[simp] theorem norm_retagStarAlgHom (h : IsCStarNorm p) (a : A) :
    ‖retagStarAlgHom h a‖ = p a := rfl

/-- The retagging read backwards, as a ⋆-algebra homomorphism.  The partner of
`retagStarAlgHom`; a homomorphism out of the retagged algebra is a
homomorphism out of `A` composed with this. -/
def unretagStarAlgHom (h : IsCStarNorm p) : WithCStarNorm h →⋆ₐ[ℂ] A where
  toFun := id
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp] theorem unretagStarAlgHom_apply (h : IsCStarNorm p)
    (a : WithCStarNorm h) : unretagStarAlgHom h a = a := rfl

end WithCStarNorm

/-- **The chain closed: a C⋆-norm on a complex ⋆-algebra makes its completion a
C⋆-algebra.**

Every hypothesis of `CStarCompletion.completionCStarAlgebra` is discharged by
the instances above, so this is the composite

  `IsCStarNorm p` ⟶ pre-C⋆-algebra `WithCStarNorm h` ⟶ C⋆-algebra
  `Completion (WithCStarNorm h)`.

Applied to `StarRep.isCStarNorm_of_injective` for a faithful product
representation of `A ⊙ B` on `H ⊗ K`, the right-hand side is the roadmap's
`A ⊗_{π,ρ} B` as a genuine C⋆-algebra.  It is still indexed by `(π, ρ)`;
removing that index is Takesaki's theorem and is not done anywhere in this
development. -/
@[reducible] noncomputable def completionCStarAlgebraOfIsCStarNorm [StarModule ℂ A]
    (h : IsCStarNorm p) :
    CStarAlgebra (UniformSpace.Completion (WithCStarNorm h)) :=
  CStarCompletion.completionCStarAlgebra

end Bundled

end CStarTensor
end GroupApproximation
