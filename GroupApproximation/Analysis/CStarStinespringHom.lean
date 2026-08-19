import GroupApproximation.Analysis.CStarStinespringLinear
import GroupApproximation.Analysis.CStarStinespringDilation

/-!
# The Stinespring representation, bundled

## What this module provides

The operator laws proved across `CStarStinespringRep` and
`CStarStinespringLinear` assemble into a single object:

* `stinespringRepHom` -- the dilation representation as a
  ⋆-homomorphism `A →⋆ₐ[ℂ] B(K)`, where `K` is the Stinespring space;
* `stinespring_dilation_repHom` -- the dilation identity restated
  through the bundle: `V* ∘ π(c) ∘ V = φ(c)`.

This is the shape in which Stinespring's theorem is consumed: a
completely positive map is a compression of a ⋆-representation.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `RE.05`
remains **MISSING**.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace
open UniformSpace

universe u w

variable {A : Type u} [CStarAlgebra A]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (φ : A →ₗ[ℂ] (H →L[ℂ] H)) (hφ : IsCompletelyPositive φ)

/-- **The Stinespring representation, bundled**: the dilation operators
as a ⋆-homomorphism into the bounded operators on the Stinespring
space. -/
noncomputable def stinespringRepHom :
    A →⋆ₐ[ℂ] (StinespringSpace φ hφ →L[ℂ] StinespringSpace φ hφ) where
  toFun := stinespringRepOp φ hφ
  map_one' := stinespringRepOp_one φ hφ
  map_mul' := stinespringRepOp_mul φ hφ
  map_zero' := by
    have h := stinespringRepOp_smul φ hφ 0 0
    rw [zero_smul] at h
    rw [h, zero_smul]
  map_add' := stinespringRepOp_add φ hφ
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, stinespringRepOp_smul,
      stinespringRepOp_one, Algebra.algebraMap_eq_smul_one,
      ContinuousLinearMap.one_def]
  map_star' c := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun ζ η => ?_
    rw [inner_stinespringRepOp_adjoint, star_star]

@[simp] theorem stinespringRepHom_apply (c : A) :
    stinespringRepHom φ hφ c = stinespringRepOp φ hφ c := rfl

/-- **Stinespring's dilation identity, through the bundle**: every
completely positive map is the compression of a ⋆-representation. -/
theorem stinespring_dilation_repHom (c : A) :
    (ContinuousLinearMap.adjoint (stinespringV φ hφ)).comp
        ((stinespringRepHom φ hφ c).comp (stinespringV φ hφ))
      = φ c :=
  stinespring_dilation φ hφ c

end CStarExactness
end GroupApproximation
