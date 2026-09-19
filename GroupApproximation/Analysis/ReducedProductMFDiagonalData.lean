import GroupApproximation.Analysis.NormMatrixCoronaPolynomialLifts

/-!
# The double-sequence data in the reduced-product MF diagonal argument

This file performs the choice steps before the finite block-diagonal
selection.  From coordinate MF embeddings and countably many elements of the
reduced product it chooses:

* bounded lifts to the coordinate algebras;
* one MF matrix-corona model of every coordinate algebra;
* polynomial-compatible bounded matrix lifts inside every such model.

The endpoint is the exact norm identity used in the manuscript: for fixed
outer coordinate `n` and rational star polynomial `p`, the norm in `B_n` is
the limsup of the norms of the inner matrix evaluations.
-/

namespace GroupApproximation
namespace ReducedProductMFDiagonalData

open Filter
open PolarLiftingGeneralCStar
open RationalNoncommutativeStarPolynomial
open NormMatrixCoronaPolynomialLifts

noncomputable section

universe u v

/-- A single coordinate algebra's chosen MF embedding, stripped to the data
used by the diagonal proof. -/
structure CoordinateMFWitness (B : Type u) [CStarAlgebra B] where
  model : ℕ → FiniteModel
  model_nonempty : ∀ k, Nonempty (model k)
  embedding :
    letI : ∀ k, Nonempty (model k) := model_nonempty
    B →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun k ↦ model k)
  embedding_injective : Function.Injective embedding

/-- Forget the dimension normalization clauses of `HasMFEmbedding`; the
diagonal proof needs only a faithful corona embedding. -/
def CoordinateMFWitness.ofHasMFEmbedding
    {B : Type u} [CStarAlgebra B] (hB : HasMFEmbedding B) :
    CoordinateMFWitness B := by
  rcases hB with ⟨X, hne, _hpos, _hmono, e, he⟩
  exact ⟨X, hne, e, he⟩

variable (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)]
  [∀ n, Nontrivial (B n)]

/-- Chosen coordinate MF witnesses. -/
def coordinateWitness (hB : ∀ n, HasMFEmbedding (B n)) (n : ℕ) :
    CoordinateMFWitness (B n) :=
  CoordinateMFWitness.ofHasMFEmbedding (hB n)

variable {C : Type v} [CStarAlgebra C]
variable (i : C →⋆ₙₐ[ℂ] CStarProductCorona B cofinite)
variable (a : ℕ → C)

/-- A chosen bounded-coordinate lift of each element of the dense family. -/
def reducedProductGeneratorLift (j : ℕ) : BoundedCStarSequence B :=
  Function.surjInv (cStarProductCoronaQuotient_surjective B cofinite) (i (a j))

theorem reducedProductGeneratorLift_quotient (j : ℕ) :
    cStarProductCoronaQuotient B cofinite
      (reducedProductGeneratorLift B i a j) = i (a j) :=
  Function.surjInv_eq _ _

variable (hB : ∀ n, HasMFEmbedding (B n))

/-- The matrix model used at outer coordinate `n`. -/
def innerModel (n k : ℕ) : FiniteModel :=
  (coordinateWitness B hB n).model k

instance innerModelNonempty (n k : ℕ) : Nonempty (innerModel B hB n k) :=
  (coordinateWitness B hB n).model_nonempty k

/-- The chosen faithful MF embedding of `B_n`. -/
def innerEmbedding (n : ℕ) :
    B n →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun k ↦ innerModel B hB n k) :=
  (coordinateWitness B hB n).embedding

theorem innerEmbedding_injective (n : ℕ) :
    Function.Injective (innerEmbedding B hB n) :=
  (coordinateWitness B hB n).embedding_injective

/-- The manuscript's matrices `a_i^(n,k)`. -/
def innerGeneratorLift (n j : ℕ) :
    BoundedMatrixSequence (fun k ↦ innerModel B hB n k) :=
  generatorLift (fun k ↦ innerModel B hB n k) (innerEmbedding B hB n)
    (fun r ↦ reducedProductGeneratorLift B i a r n) j

/-- For fixed `n`, every polynomial in the inner matrix lifts represents the
faithful image of the same polynomial in `B_n`. -/
theorem innerPolynomial_quotient (n : ℕ) (p : Polynomial) :
    normMatrixCStarCoronaMk (fun k ↦ innerModel B hB n k)
        (eval (innerGeneratorLift B i a hB n) p) =
      innerEmbedding B hB n
        (eval (fun j ↦ reducedProductGeneratorLift B i a j n) p) :=
  polynomialLift_quotient (fun k ↦ innerModel B hB n k)
    (innerEmbedding B hB n)
    (fun j ↦ reducedProductGeneratorLift B i a j n) p

/-- **The fixed-outer-coordinate norm identity in the manuscript.**  The
norm of a rational star polynomial in `B_n` is the limsup of its norms in the
chosen inner matrix lifts. -/
theorem norm_innerPolynomial_eq_limsup (n : ℕ) (p : Polynomial) :
    ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n) p‖ =
      Filter.limsup
        (fun k ↦ ‖eval (fun j ↦ innerGeneratorLift B i a hB n j k) p‖)
        cofinite := by
  have hiso := NonUnitalStarAlgHom.isometry (innerEmbedding B hB n)
    (innerEmbedding_injective B hB n)
  rw [← hiso.norm_map]
  rw [← innerPolynomial_quotient B i a hB n p]
  rw [norm_filterMatrixCorona_mk_eq_limsup]
  congr 1
  funext k
  exact congrArg norm
    (eval_generatorLift_apply (fun r ↦ innerModel B hB n r)
      (innerEmbedding B hB n)
      (fun j ↦ reducedProductGeneratorLift B i a j n) p k)

end

end ReducedProductMFDiagonalData
end GroupApproximation
