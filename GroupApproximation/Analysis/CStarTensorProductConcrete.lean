import GroupApproximation.Analysis.CStarTensorProductSpatial
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Concretely represented C⋆-algebras and the cross-norm property

## Why this file exists

`CStarTensorProductSpatial.lean` builds the spatial norm for a pair of
⋆-representations by *adjointable operators on an inner product space*.  That
generality is what removes the need for a Hilbert-space completion, but it
raises two obligations which this file discharges:

1. **Non-vacuity.**  The abstract notion `StarRep` must be inhabited by the
   objects the manuscript actually deals with.  `StarRep.ofStarAlgHom` shows
   that every ⋆-homomorphism of a complex ⋆-algebra into `B(H)` for a
   *Hilbert* space `H` is a `StarRep`: `star` in `B(H)` is the adjoint, which
   is exactly the `IsAdjoint` relation.  So concretely represented
   C⋆-algebras --- among them the reduced group C⋆-algebras of this
   repository, which are closed ⋆-subalgebras of `B(ℓ²G)` --- are covered.

2. **The genuine cross-norm statement.**  In the general setting the best
   available statement is `‖a ⊗ₜ b‖ = ‖π a‖ * ‖ρ b‖`, because for incomplete
   `H` the algebra `H →L[ℂ] H` need not be a C⋆-algebra and a faithful
   ⋆-homomorphism into it need not be isometric.  For Hilbert `H` it *is*
   isometric (`NonUnitalStarAlgHom.norm_map`), so the spatial norm satisfies
   the textbook identity `‖a ⊗ₜ b‖ = ‖a‖ * ‖b‖`.  That is
   `spatialNorm_tmul_of_injective`, and it is the cross-norm axiom of a
   C⋆-tensor norm.

## What is still missing

An earlier version of this paragraph grouped two things together and was wrong
to: it said faithfulness of `π ⊗ ρ` on *all* of `A ⊗[ℂ] B` and independence of
the norm from `(π, ρ)` "are both the slice-map/Takesaki circle of ideas, and
neither is proved here".  They are not the same circle of ideas.

* **Faithfulness on all of `A ⊗[ℂ] B` is now proved**, as
  `CStarTensorProductSpatial.spatialHom_injective`.  It needs no states, no
  GNS and no continuity --- only that the vector functionals separate points,
  plus a Hamel basis on one factor.  So `spatialNorm_tmul_ne_zero` below,
  which sees only elementary tensors, is no longer the best available
  non-degeneracy statement; `CStarTensorProductSpatial.spatialNorm_isCStarNorm`
  is.
* **Independence of the norm from `(π, ρ)` is still missing**, and *that* is
  the Takesaki theorem, which genuinely does need states, GNS and continuous
  slice maps.

Until independence is proved the spatial norm is a fully constructed C⋆-norm
attached to a chosen pair of faithful representations, not a canonical
`⊗_min`.  See the roadmap in `CStarTensorProduct.lean`.

## Manuscript status

Infrastructure; certifies no manuscript step.  The exactness and nuclearity
rows of `non_mf_groups_exist.tex` remain **MISSING**.
-/

namespace GroupApproximation
namespace CStarTensor

open scoped InnerProductSpace TensorProduct

universe u v w x

/-! ## ⋆-representations on Hilbert spaces -/

/-- **A ⋆-homomorphism into `B(H)` for a Hilbert space `H` is a
⋆-representation** in the sense of `StarRep`.  The `IsAdjoint` field is the
defining property of the adjoint, since `star` on `H →L[ℂ] H` *is* the
adjoint. -/
noncomputable def StarRep.ofStarAlgHom {A : Type u} [Ring A] [StarRing A]
    [Algebra ℂ A] {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : StarRep A H where
  hom := φ.toAlgHom
  isAdjoint_star a := by
    intro x y
    have h1 : (φ.toAlgHom) (star a)
        = ContinuousLinearMap.adjoint (φ.toAlgHom a) := by
      show φ (star a) = ContinuousLinearMap.adjoint (φ a)
      rw [map_star, ContinuousLinearMap.star_eq_adjoint]
    rw [h1, ContinuousLinearMap.adjoint_inner_right]

@[simp] theorem StarRep.ofStarAlgHom_hom_apply {A : Type u} [Ring A] [StarRing A]
    [Algebra ℂ A] {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    (StarRep.ofStarAlgHom φ).hom a = φ a := rfl

/-- The bounded operators on a Hilbert space, represented on that space by the
identity.  Recorded so that `StarRep` is visibly inhabited. -/
noncomputable def StarRep.self (H : Type w) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : StarRep (H →L[ℂ] H) H :=
  StarRep.ofStarAlgHom (StarAlgHom.id ℂ (H →L[ℂ] H))

/-! ## The cross-norm property -/

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
variable {H : Type w} {K : Type x} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **The spatial norm of a faithfully represented pair is a cross norm**:
`‖a ⊗ₜ b‖ = ‖a‖ * ‖b‖`.

Two inputs combine: `norm_mapL`, which says `‖S ⊗ T‖ = ‖S‖ * ‖T‖` for the
operator norms (Mathlib gives only `≤`), and the fact that an injective
⋆-homomorphism of C⋆-algebras is isometric, which is Mathlib's
`NonUnitalStarAlgHom.norm_map`. -/
theorem spatialNorm_tmul_of_injective (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ψ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) (a : A) (b : B) :
    spatialNorm (StarRep.ofStarAlgHom φ) (StarRep.ofStarAlgHom ψ)
        (a ⊗ₜ[ℂ] b) = ‖a‖ * ‖b‖ := by
  rw [spatialNorm_tmul, StarRep.ofStarAlgHom_hom_apply,
    StarRep.ofStarAlgHom_hom_apply, NonUnitalStarAlgHom.norm_map φ hφ a,
    NonUnitalStarAlgHom.norm_map ψ hψ b]

/-- The spatial norm does not degenerate on nonzero elementary tensors.  This
is the first genuine non-degeneracy statement about the norm; full
definiteness on `A ⊗[ℂ] B` needs the slice-map argument and is not proved. -/
theorem spatialNorm_tmul_ne_zero (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ψ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) {a : A} {b : B} (ha : a ≠ 0) (hb : b ≠ 0) :
    spatialNorm (StarRep.ofStarAlgHom φ) (StarRep.ofStarAlgHom ψ)
        (a ⊗ₜ[ℂ] b) ≠ 0 := by
  rw [spatialNorm_tmul_of_injective φ ψ hφ hψ a b]
  exact mul_ne_zero (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb)

/-- The spatial norm of a pair of faithfully represented C⋆-algebras is a
C⋆-seminorm on the algebraic tensor product.  Restatement of
`spatialNorm_isCStarSeminorm` in the concrete setting, for use downstream. -/
theorem spatialNorm_isCStarSeminorm_of_starAlgHom (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ψ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    IsCStarSeminorm
      (spatialNorm (StarRep.ofStarAlgHom φ) (StarRep.ofStarAlgHom ψ)) :=
  spatialNorm_isCStarSeminorm _ _

end CStarTensor
end GroupApproximation
