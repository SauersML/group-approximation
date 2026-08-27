import GroupApproximation.Analysis.CStarTensorProductConcrete
import GroupApproximation.Analysis.CStarNormBundled
import GroupApproximation.Analysis.CStarCompletionCoe

/-!
# The spatial tensor product `A ⊗_{π,ρ} B`, assembled as a C⋆-algebra

## What this module is

The tensor lane proved, in order: the spatial seminorm of a pair of
⋆-representations is a C⋆-seminorm (`CStarTensorProductSpatial`), it is a
C⋆-*norm* when both representations are faithful (`spatialNorm_isCStarNorm`,
via `spatialHom_injective`), a C⋆-norm retags its algebra into a pre-C⋆-algebra
(`CStarNormBundled.WithCStarNorm`), and the completion of a pre-C⋆-algebra is a
C⋆-algebra (`CStarCompletion.completionCStarAlgebra`, packaged as
`completionCStarAlgebraOfIsCStarNorm`).

What no module did is *say the sentence*: fix the pair `(π, ρ)`, apply the
chain, and name the result.  This module says it.  `SpatialTensorProduct π ρ hπ
hρ` is a C⋆-algebra containing the algebraic tensor product `A ⊙ B` as a dense
⋆-subalgebra via the isometric ⋆-homomorphism `spatialTensorIn`, with the
cross-seminorm value `‖a ⊗ₜ b‖ = ‖π.hom a‖ * ‖ρ.hom b‖` on elementary tensors.
This closes the assembly step of the roadmap in `CStarTensorProduct.lean`:
Stages A and B are now both done *and joined*.

## What this module is not

It is **not** `⊗_min`.  The object is indexed by the chosen pair `(π, ρ)`;
independence of that choice is Takesaki's theorem (Stage C of the roadmap) and
is proved nowhere in this development.  Writing `⊗_min` for this object would
lie about canonicity, so the name keeps the index.

The elementary-tensor norm is stated against `‖π.hom a‖`, not `‖a‖`: at this
level of generality `A` is a complex ⋆-algebra with no norm of its own.  When
`A` is a C⋆-algebra, `π` lands in `B(H)` for complete `H`, and `π` is
injective, the two agree because injective ⋆-homomorphisms of C⋆-algebras are
isometric; that upgrade belongs to the consumer that fixes such a context.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `SO.16` (exactness)
and `RE.05` (nuclearity) remain **MISSING**: exactness needs the canonical
`⊗_min` (Takesaki) and the noncommutative C⋆-quotient, nuclearity needs the
maximal norm besides.  What this module changes is that "`A ⊗_{π,ρ} B` as a
genuine C⋆-algebra", promised by the roadmap's honest verdict as the yield of
Stages A + B, now actually exists as a declaration rather than as a corollary
a reader must assemble.
-/

namespace GroupApproximation
namespace CStarTensor

open UniformSpace

open scoped TensorProduct

universe u v w x

variable {A : Type u} {B : Type v} [Ring A] [StarRing A] [Algebra ℂ A]
  [StarModule ℂ A] [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
variable {H : Type w} {K : Type x} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-! ## The object

The retagging arrow this module introduced, `WithCStarNorm.retagStarAlgHom`,
now lives in `CStarNormBundled` beside the synonym it retags and its inverse
`unretagStarAlgHom`; it moved in one commit so no call site changed. -/

variable (π : StarRep A H) (ρ : StarRep B K)
variable (hπ : Function.Injective π.hom) (hρ : Function.Injective ρ.hom)

/-- The algebraic tensor product `A ⊙ B`, retagged with the spatial C⋆-norm of
the faithful pair `(π, ρ)`.  A pre-C⋆-algebra: every C⋆-axiom holds, only
completeness is missing. -/
abbrev SpatialPreTensor : Type (max u v) :=
  WithCStarNorm (spatialNorm_isCStarNorm π ρ hπ hρ)

/-- **The spatial tensor product `A ⊗_{π,ρ} B`**: the completion of the
algebraic tensor product in the spatial C⋆-norm of the faithful pair
`(π, ρ)`.  A C⋆-algebra by the instance below.

Deliberately indexed by the pair: independence of the choice is Takesaki's
theorem and is not proved in this development, so the notation `⊗_min` is not
available for it. -/
def SpatialTensorProduct : Type (max u v) :=
  Completion (SpatialPreTensor π ρ hπ hρ)

/-- The spatial tensor product is a C⋆-algebra: the completion chain of
`CStarNormBundled` applied to the spatial C⋆-norm. -/
noncomputable instance instCStarAlgebraSpatialTensorProduct :
    CStarAlgebra (SpatialTensorProduct π ρ hπ hρ) :=
  completionCStarAlgebraOfIsCStarNorm (spatialNorm_isCStarNorm π ρ hπ hρ)

/-! ## The canonical embedding -/

/-- The canonical ⋆-algebra homomorphism from the algebraic tensor product into
the spatial tensor product: retag, then include into the completion. -/
noncomputable def spatialTensorIn :
    (A ⊗[ℂ] B) →⋆ₐ[ℂ] SpatialTensorProduct π ρ hπ hρ :=
  (CStarCompletion.coeStarAlgHom (SpatialPreTensor π ρ hπ hρ)).comp
    (WithCStarNorm.retagStarAlgHom (spatialNorm_isCStarNorm π ρ hπ hρ))

/-- The canonical embedding computes the spatial norm: it is isometric onto
its image, with the algebraic tensor product carrying `spatialNorm π ρ`. -/
theorem norm_spatialTensorIn (x : A ⊗[ℂ] B) :
    ‖spatialTensorIn π ρ hπ hρ x‖ = spatialNorm π ρ x :=
  Completion.norm_coe _

/-- **The cross-seminorm value on elementary tensors**, inside the completed
algebra: `‖a ⊗ₜ b‖ = ‖π.hom a‖ * ‖ρ.hom b‖`. -/
theorem norm_spatialTensorIn_tmul (a : A) (b : B) :
    ‖spatialTensorIn π ρ hπ hρ (a ⊗ₜ[ℂ] b)‖ = ‖π.hom a‖ * ‖ρ.hom b‖ := by
  rw [norm_spatialTensorIn, spatialNorm_tmul]

/-- The canonical embedding is injective: the spatial norm is definite for a
faithful pair, and the inclusion into the completion is isometric. -/
theorem spatialTensorIn_injective :
    Function.Injective (spatialTensorIn π ρ hπ hρ) := by
  intro x y hxy
  have hz : ‖spatialTensorIn π ρ hπ hρ (x - y)‖ = 0 := by
    rw [map_sub, hxy, sub_self, norm_zero]
  rw [norm_spatialTensorIn] at hz
  exact sub_eq_zero.mp ((spatialNorm_isCStarNorm π ρ hπ hρ).eq_zero _ hz)

/-- The algebraic tensor product is dense in the spatial tensor product. -/
theorem denseRange_spatialTensorIn :
    DenseRange (spatialTensorIn π ρ hπ hρ) :=
  Completion.denseRange_coe.comp
    (WithCStarNorm.retagStarAlgHom_surjective
      (spatialNorm_isCStarNorm π ρ hπ hρ)).denseRange
    (Completion.continuous_coe _)

end CStarTensor
end GroupApproximation
