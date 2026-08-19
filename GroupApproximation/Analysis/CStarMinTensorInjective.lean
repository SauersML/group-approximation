import GroupApproximation.Analysis.CStarTakesakiIdentification
import GroupApproximation.Analysis.CStarMinTensorQuotient

/-!
# Injectivity of the minimal tensor norm

## What this module builds

`SO.16` (`p:E-exact`) asks for exactness of `C⋆_red(E)`.  The exactness
predicate itself is `CStarMinTensorQuotient.IsExactCStar`; what the row's
standing note records as missing is a *theory* around it -- in particular the
permanence properties through which Kirchberg--Wassermann carries exactness
from a large algebra to a subalgebra.  The structural input of every such
argument is that `⊗_min` is **injective**: an inclusion of C⋆-algebras induces
an isometric inclusion of minimal tensor products.  That is what this module
proves.

* `spatialHom_tensorStarAlgHomMap` -- restricting a representation along a
  ⋆-homomorphism `ι` and then forming the product representation gives the
  *same operator* as forming the product representation and precomposing with
  `ι ⊗ id`.  Both sides are operators on the same space `H ⊗ K`, so this is an
  identity, not a comparison;
* `minTensorNorm_tensorStarAlgHomMap_of_injective` -- **injectivity of the
  minimal norm**: for injective `ι : A →⋆ₐ C` and any faithful representations
  of `C` and of the second factor `B` on complete Hilbert spaces,
  `‖(ι ⊗ id) x‖_min = ‖x‖_min`.  Two applications of Takesaki's identification
  (`CStarTakesakiIdentification.spatialNorm_eq_minTensorNorm`), one at
  `(π, ρ)` and one at `(π ∘ ι, ρ)`, with the operator identity above in
  between;
* `minTensorNorm_inclusion_of_faithful` -- the same statement for an inclusion
  `S ≤ T` of closed ⋆-subalgebras of `B(H)`, where the faithful
  representations are the two subtype maps and no extra hypothesis is needed;
* `minTensorInclusion` -- the induced ⋆-homomorphism
  `A ⊗_min B → C ⊗_min B` of the completions, with `norm_minTensorInclusion`
  (it is isometric) and `minTensorInclusion_injective`.

## What is claimed and what is not

Injectivity of `⊗_min` is one of the two ingredients of "a subalgebra of an
exact C⋆-algebra is exact".  The other is the slice-map (Fubini) identity
`closure (I ⊙ C) ∩ (B ⊗_min A) = closure (I ⊙ A)`, which is **not** proved
here and for which this development has no vocabulary.  So no algebra becomes
exact because of this module, and in particular the Kirchberg--Wassermann
crossover -- for a discrete group `E`, exactness of `E` iff exactness of
`C⋆_red(E)` -- acquires no formal counterpart.  What changes is that the
transport step of that argument is now available in the form the argument
uses it: the inclusion `C⋆_red(G) ⊆ C⋆_u(|G|)` induces an isometric inclusion
after tensoring, so the two algebras' minimal tensor norms are *the same
norm*, which is exactly what lets exactness descend once the slice identity
is available.

The faithful-representation hypotheses are not a restriction in the cases the
manuscript cares about: the algebras of this repository are concrete algebras
of operators on `ℓ²(G)`, whose subtype maps are faithful by construction, and
`minTensorNorm_inclusion_of_faithful` is stated so that they are discharged
automatically.

## Manuscript status

Infrastructure.  `SO.16` keeps its grade: property A of the group is proved
(`ExactnessPermanence`), the crossover to the algebra is not, and nothing
here asserts exactness of any algebra.
-/

namespace GroupApproximation
namespace CStarTensor

open CStarState
open scoped TensorProduct

universe u v w x y

/-! ## Restriction along a ⋆-homomorphism -/

/-- **Restricting the left leg**: the product representation of the restricted
representation `π ∘ ι` at `x` is the product representation of `π` at
`(ι ⊗ id) x`.  Both sides are operators on `H ⊗ K`; the proof is the tensor
induction, with the elementary-tensor case an identity of `mapL`s. -/
theorem spatialHom_tensorStarAlgHomMap
    {A : Type u} {C : Type v} {B : Type w}
    [CStarAlgebra A] [CStarAlgebra C] [CStarAlgebra B]
    {H : Type x} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {K : Type y} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (ι : A →⋆ₐ[ℂ] C) (π : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : StarRep B K)
    (x : A ⊗[ℂ] B) :
    spatialHom (StarRep.ofStarAlgHom (π.comp ι)) ρ x
      = spatialHom (StarRep.ofStarAlgHom π) ρ
          (tensorStarAlgHomMap (C := B) ι x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
      have hmap : tensorStarAlgHomMap (C := B) ι (a ⊗ₜ[ℂ] b)
          = (ι a) ⊗ₜ[ℂ] b :=
        Algebra.TensorProduct.map_tmul ι.toAlgHom (AlgHom.id ℂ B) a b
      calc spatialHom (StarRep.ofStarAlgHom (π.comp ι)) ρ (a ⊗ₜ[ℂ] b)
          = TensorProduct.mapL
              ((StarRep.ofStarAlgHom (π.comp ι)).hom a) (ρ.hom b) :=
            spatialHom_tmul _ _ a b
        _ = TensorProduct.mapL ((StarRep.ofStarAlgHom π).hom (ι a)) (ρ.hom b) :=
            rfl
        _ = spatialHom (StarRep.ofStarAlgHom π) ρ ((ι a) ⊗ₜ[ℂ] b) :=
            (spatialHom_tmul _ _ (ι a) b).symm
        _ = spatialHom (StarRep.ofStarAlgHom π) ρ
              (tensorStarAlgHomMap (C := B) ι (a ⊗ₜ[ℂ] b)) := by
            rw [hmap]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The spatial *norm* form of the restriction identity. -/
theorem spatialNorm_tensorStarAlgHomMap
    {A : Type u} {C : Type v} {B : Type w}
    [CStarAlgebra A] [CStarAlgebra C] [CStarAlgebra B]
    {H : Type x} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {K : Type y} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (ι : A →⋆ₐ[ℂ] C) (π : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : StarRep B K)
    (x : A ⊗[ℂ] B) :
    spatialNorm (StarRep.ofStarAlgHom (π.comp ι)) ρ x
      = spatialNorm (StarRep.ofStarAlgHom π) ρ
          (tensorStarAlgHomMap (C := B) ι x) := by
  rw [spatialNorm_apply, spatialNorm_apply,
    spatialHom_tensorStarAlgHomMap ι π ρ x]

/-! ## Injectivity of the minimal norm -/

/-- **The minimal tensor norm is injective.**  If `ι : A →⋆ₐ C` is injective
and `C`, `B` admit faithful unital ⋆-representations on complete Hilbert
spaces, then `ι ⊗ id` is isometric for the minimal norms.

The proof is Takesaki's identification used twice.  On the `C`-side the
minimal norm of `(ι ⊗ id) x` is the spatial norm of the faithful pair
`(π, ρ)`; on the `A`-side the minimal norm of `x` is the spatial norm of the
faithful pair `(π ∘ ι, ρ)` -- faithful precisely because `ι` is injective --
and the two spatial norms are the norm of *one and the same operator* by
`spatialNorm_tensorStarAlgHomMap`. -/
theorem minTensorNorm_tensorStarAlgHomMap_of_injective
    {A : Type u} {C : Type v} {B : Type w}
    [CStarAlgebra A] [CStarAlgebra C] [CStarAlgebra B]
    [Nontrivial A] [Nontrivial C] [Nontrivial B]
    {H : Type x} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {K : Type y} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    (ι : A →⋆ₐ[ℂ] C) (hι : Function.Injective ι)
    (π : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : Function.Injective π)
    (ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (hρ : Function.Injective ρ)
    (x : A ⊗[ℂ] B) :
    minTensorNorm (tensorStarAlgHomMap (C := B) ι x) = minTensorNorm x := by
  have hcomp : Function.Injective (π.comp ι) := by
    intro a b hab
    apply hι
    apply hπ
    exact hab
  have h1 : spatialNorm (StarRep.ofStarAlgHom π) (StarRep.ofStarAlgHom ρ)
      (tensorStarAlgHomMap (C := B) ι x)
      = minTensorNorm (tensorStarAlgHomMap (C := B) ι x) :=
    spatialNorm_eq_minTensorNorm π ρ hπ hρ _
  have h2 : spatialNorm (StarRep.ofStarAlgHom (π.comp ι))
      (StarRep.ofStarAlgHom ρ) x = minTensorNorm x :=
    spatialNorm_eq_minTensorNorm (π.comp ι) ρ hcomp hρ x
  rw [← h1, ← h2]
  exact (spatialNorm_tensorStarAlgHomMap ι π (StarRep.ofStarAlgHom ρ) x).symm

/-- **Injectivity of `⊗_min` for an inclusion of closed ⋆-subalgebras of
`B(H)`.**  The faithful representations are the subtype maps, so the only
hypothesis left is faithfulness for the second factor. -/
theorem minTensorNorm_inclusion_of_faithful
    {H : Type x} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {B : Type w} [CStarAlgebra B] [Nontrivial B]
    {K : Type y} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    (S T : StarSubalgebra ℂ (H →L[ℂ] H)) (hST : S ≤ T)
    [IsClosed (S : Set (H →L[ℂ] H))] [IsClosed (T : Set (H →L[ℂ] H))]
    [Nontrivial S] [Nontrivial T]
    (ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (hρ : Function.Injective ρ)
    (x : S ⊗[ℂ] B) :
    minTensorNorm
        (tensorStarAlgHomMap (C := B) (StarSubalgebra.inclusion hST) x)
      = minTensorNorm x :=
  minTensorNorm_tensorStarAlgHomMap_of_injective
    (StarSubalgebra.inclusion hST) (StarSubalgebra.inclusion_injective hST)
    T.subtype (fun _ _ hab => Subtype.ext hab) ρ hρ x

/-! ## The isometric inclusion of the completions -/

section Inclusion

variable {A : Type u} {C : Type v} {B : Type w}
  [CStarAlgebra A] [CStarAlgebra C] [CStarAlgebra B]
  [Nontrivial A] [Nontrivial C] [Nontrivial B]

/-- The pre-completion inclusion: unretag, apply `ι ⊗ id`, land in the
completed target. -/
noncomputable def minPreInclusion (ι : A →⋆ₐ[ℂ] C) :
    (MinPreTensor A B) →⋆ₐ[ℂ] MinTensorProduct C B :=
  ((minTensorIn C B).comp (tensorStarAlgHomMap (C := B) ι)).comp
    (WithCStarNorm.unretagStarAlgHom isCStarNorm_minTensorNorm)

/-- The pre-completion inclusion is isometric as soon as `ι ⊗ id` preserves
the minimal norm -- which `minTensorNorm_tensorStarAlgHomMap_of_injective`
supplies for injective `ι`. -/
theorem norm_minPreInclusion (ι : A →⋆ₐ[ℂ] C)
    (hnorm : ∀ y : A ⊗[ℂ] B,
      minTensorNorm (tensorStarAlgHomMap (C := B) ι y) = minTensorNorm y)
    (x : MinPreTensor A B) :
    ‖minPreInclusion (B := B) ι x‖ = ‖x‖ := by
  show ‖minTensorIn C B (tensorStarAlgHomMap (C := B) ι
      (WithCStarNorm.unretagStarAlgHom isCStarNorm_minTensorNorm x))‖ = ‖x‖
  rw [norm_minTensorIn]
  exact hnorm _

/-- **The inclusion `A ⊗_min B → C ⊗_min B`**, the isometric extension of
`ι ⊗ id` across the completion. -/
noncomputable def minTensorInclusion (ι : A →⋆ₐ[ℂ] C)
    (hnorm : ∀ y : A ⊗[ℂ] B,
      minTensorNorm (tensorStarAlgHomMap (C := B) ι y) = minTensorNorm y) :
    MinTensorProduct A B →⋆ₐ[ℂ] MinTensorProduct C B :=
  CStarCompletion.extendStarAlgHom (minPreInclusion (B := B) ι)
    (CStarCompletion.uniformContinuous_of_norm_le _
      fun x => le_of_eq (norm_minPreInclusion (B := B) ι hnorm x))

/-- On the algebraic tensor product the inclusion is `ι ⊗ id`. -/
theorem minTensorInclusion_minTensorIn (ι : A →⋆ₐ[ℂ] C)
    (hnorm : ∀ y : A ⊗[ℂ] B,
      minTensorNorm (tensorStarAlgHomMap (C := B) ι y) = minTensorNorm y)
    (x : A ⊗[ℂ] B) :
    minTensorInclusion (B := B) ι hnorm (minTensorIn A B x)
      = minTensorIn C B (tensorStarAlgHomMap (C := B) ι x) := by
  show CStarCompletion.extendStarAlgHom _ _ (minTensorIn A B x) = _
  exact CStarCompletion.extendStarAlgHom_coe _ _ _

/-- The inclusion is continuous. -/
theorem continuous_minTensorInclusion (ι : A →⋆ₐ[ℂ] C)
    (hnorm : ∀ y : A ⊗[ℂ] B,
      minTensorNorm (tensorStarAlgHomMap (C := B) ι y) = minTensorNorm y) :
    Continuous (minTensorInclusion (B := B) ι hnorm) :=
  UniformSpace.Completion.continuous_extension
    (f := ((minPreInclusion (B := B) ι :
        MinPreTensor A B →⋆ₐ[ℂ] MinTensorProduct C B) :
      MinPreTensor A B → MinTensorProduct C B))

/-- **The inclusion of minimal tensor products is isometric.**  It is
isometric on the dense algebraic part by hypothesis, and the set where a
continuous map preserves norms is closed. -/
theorem norm_minTensorInclusion (ι : A →⋆ₐ[ℂ] C)
    (hnorm : ∀ y : A ⊗[ℂ] B,
      minTensorNorm (tensorStarAlgHomMap (C := B) ι y) = minTensorNorm y)
    (z : MinTensorProduct A B) :
    ‖minTensorInclusion (B := B) ι hnorm z‖ = ‖z‖ := by
  refine (denseRange_minTensorIn (A := A) (B := B)).induction_on z ?_ ?_
  · exact isClosed_eq
      (continuous_norm.comp (continuous_minTensorInclusion (B := B) ι hnorm))
      continuous_norm
  · intro x
    rw [minTensorInclusion_minTensorIn, norm_minTensorIn, norm_minTensorIn,
      hnorm]

/-- The inclusion of minimal tensor products is injective. -/
theorem minTensorInclusion_injective (ι : A →⋆ₐ[ℂ] C)
    (hnorm : ∀ y : A ⊗[ℂ] B,
      minTensorNorm (tensorStarAlgHomMap (C := B) ι y) = minTensorNorm y) :
    Function.Injective (minTensorInclusion (B := B) ι hnorm) := by
  intro z w hzw
  have hz : ‖z - w‖ = 0 := by
    rw [← norm_minTensorInclusion (B := B) ι hnorm (z - w), map_sub, hzw,
      sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end Inclusion

end CStarTensor
end GroupApproximation
