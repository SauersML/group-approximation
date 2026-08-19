import GroupApproximation.Analysis.CStarTakesakiCyclic

/-!
# Takesaki's identification: the spatial norm of a faithful pair is the
# minimal norm

## The theorem

For unital C⋆-algebras `A`, `B` and unital ⋆-representations on complete
Hilbert spaces:

* `spatialNorm_le_minTensorNorm` --- for **any** pair (no faithfulness),
  the spatial norm is dominated by the canonical minimal norm;
* `spatialNorm_eq_minTensorNorm` --- for a **faithful** pair, they are
  equal.

This closes Stage C.4 of the tensor-lane roadmap (`CStarTensorProduct`):
the norm the completion `MinTensorProduct` carries can now honestly be
computed in any single faithful representation pair, which is what lets
`⊗_min` be evaluated on concrete operators --- e.g. on the reduced group
C⋆-algebra in its regular representation.

## The two halves

The domination `min ≤ spatial-of-faithful` is `CStarTakesakiMinLe` (the
positivity-transfer argument).  The reverse `spatial ≤ min` combines the
one-leg domination of `CStarTakesakiCyclic` with the **flip symmetry**
proved here: the Hilbert-space flip `H ⊗ K ≃ₗᵢ K ⊗ H` intertwines the
product representation of `x` with that of the flipped tensor, so the
one-leg argument applied twice --- once on each side, through the flip ---
reduces an arbitrary pair to GNS pairs, whose supremum is the minimal norm
by definition.

## What is deliberately not claimed

Minimality --- that `minTensorNorm` is the least C⋆-norm on `A ⊙ B` ---
remains open; this module identifies the canonical norm with the spatial
norms, it does not compare it with abstract C⋆-norms.  No manuscript row
changes grade here: `SO.16`/`RE.05` still await their own inputs, as
recorded in `CStarExactness.lean`.
-/

namespace GroupApproximation
namespace CStarTensor

open CStarState
open scoped InnerProductSpace TensorProduct

universe u v w x

/-! ## The flip symmetry -/

section Flip

variable {A : Type u} {B : Type v} [Ring A] [StarRing A] [Algebra ℂ A]
  [StarModule ℂ A] [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
variable {H : Type w} {K : Type x} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The Hilbert flip intertwines the product representations of a tensor
and its flip. -/
theorem spatialHom_comm_apply (π : StarRep A H) (ρ : StarRep B K)
    (y : A ⊗[ℂ] B) (w : H ⊗[ℂ] K) :
    (TensorProduct.commIsometry ℂ H K) (spatialHom π ρ y w)
      = spatialHom ρ π (Algebra.TensorProduct.comm ℂ A B y)
          ((TensorProduct.commIsometry ℂ H K) w) := by
  induction y using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero, zero_apply]
  | tmul c d =>
      rw [Algebra.TensorProduct.comm_tmul, spatialHom_tmul, spatialHom_tmul]
      induction w using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul u v =>
          rw [TensorProduct.mapL_tmul, TensorProduct.commIsometry_apply,
            TensorProduct.commIsometry_apply, TensorProduct.comm_tmul,
            TensorProduct.comm_tmul, TensorProduct.mapL_tmul]
      | add w₁ w₂ h₁ h₂ =>
          simp only [map_add, h₁, h₂]
  | add y z hy hz =>
      simp only [map_add, add_apply, hy, hz]

/-- **The flip symmetry of the spatial norm**: the spatial norm of the
flipped pair at the flipped tensor is the spatial norm of the pair. -/
theorem spatialNorm_comm (π : StarRep A H) (ρ : StarRep B K)
    (x : A ⊗[ℂ] B) :
    spatialNorm ρ π (Algebra.TensorProduct.comm ℂ A B x)
      = spatialNorm π ρ x := by
  rw [spatialNorm_apply, spatialNorm_apply]
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
    have h0 := spatialHom_comm_apply π ρ x
      ((TensorProduct.commIsometry ℂ H K).symm z)
    rw [(TensorProduct.commIsometry ℂ H K).apply_symm_apply] at h0
    rw [← h0, (TensorProduct.commIsometry ℂ H K).norm_map]
    calc ‖spatialHom π ρ x ((TensorProduct.commIsometry ℂ H K).symm z)‖
        ≤ ‖spatialHom π ρ x‖
            * ‖(TensorProduct.commIsometry ℂ H K).symm z‖ :=
          (spatialHom π ρ x).le_opNorm _
      _ = ‖spatialHom π ρ x‖ * ‖z‖ := by
          rw [(TensorProduct.commIsometry ℂ H K).symm.norm_map]
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
    have h0 := spatialHom_comm_apply π ρ x z
    have h1 : ‖spatialHom π ρ x z‖
        = ‖spatialHom ρ π (Algebra.TensorProduct.comm ℂ A B x)
            ((TensorProduct.commIsometry ℂ H K) z)‖ := by
      rw [← h0, (TensorProduct.commIsometry ℂ H K).norm_map]
    rw [h1]
    calc ‖spatialHom ρ π (Algebra.TensorProduct.comm ℂ A B x)
          ((TensorProduct.commIsometry ℂ H K) z)‖
        ≤ ‖spatialHom ρ π (Algebra.TensorProduct.comm ℂ A B x)‖
            * ‖(TensorProduct.commIsometry ℂ H K) z‖ :=
          (spatialHom ρ π _).le_opNorm _
      _ = ‖spatialHom ρ π (Algebra.TensorProduct.comm ℂ A B x)‖ * ‖z‖ := by
          rw [(TensorProduct.commIsometry ℂ H K).norm_map]

end Flip

/-! ## The identification -/

section Identification

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
  [Nontrivial A] [Nontrivial B]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {K : Type x} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

/-- **The easy half of Takesaki's identification, made unconditional**: the
spatial norm of *any* pair of ⋆-representations on complete Hilbert spaces
is dominated by the canonical minimal norm.  Both legs are reduced to GNS
legs by the one-leg domination, the second through the flip symmetry. -/
theorem spatialNorm_le_minTensorNorm (π : StarRep A H) (ρ : StarRep B K)
    (x : A ⊗[ℂ] B) : spatialNorm π ρ x ≤ minTensorNorm x := by
  refine (spatialNorm_le_leftGnsSup π ρ x).trans ?_
  refine ciSup_le fun φ => ?_
  have h1 : spatialNorm φ.gnsRep ρ x
      = spatialNorm ρ φ.gnsRep (Algebra.TensorProduct.comm ℂ A B x) :=
    (spatialNorm_comm φ.gnsRep ρ x).symm
  rw [h1]
  refine (spatialNorm_le_leftGnsSup ρ φ.gnsRep
    (Algebra.TensorProduct.comm ℂ A B x)).trans ?_
  refine ciSup_le fun ψ => ?_
  have h2 : spatialNorm ψ.gnsRep φ.gnsRep
      (Algebra.TensorProduct.comm ℂ A B x)
      = spatialNorm φ.gnsRep ψ.gnsRep x :=
    spatialNorm_comm φ.gnsRep ψ.gnsRep x
  rw [h2]
  rw [minTensorNorm_apply]
  exact le_ciSup (bddAbove_spatialNorm_gnsRep x)
    ((φ, ψ) : State A × State B)

/-- **Takesaki's identification** (Stage C.4): for a faithful pair of
unital ⋆-representations on complete Hilbert spaces, the spatial norm *is*
the canonical minimal tensor norm.  The notation `⊗_min` is henceforth
computable in any single faithful pair. -/
theorem spatialNorm_eq_minTensorNorm (π₀ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ₀ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (hπ₀ : Function.Injective π₀)
    (hρ₀ : Function.Injective ρ₀) (x : A ⊗[ℂ] B) :
    spatialNorm (StarRep.ofStarAlgHom π₀) (StarRep.ofStarAlgHom ρ₀) x
      = minTensorNorm x :=
  le_antisymm
    (spatialNorm_le_minTensorNorm (StarRep.ofStarAlgHom π₀)
      (StarRep.ofStarAlgHom ρ₀) x)
    (minTensorNorm_le_spatialNorm π₀ ρ₀ hπ₀ hρ₀ x)

/-- The norm of the canonical embedding into `A ⊗_min B`, computed in any
faithful pair: the form in which the identification is consumed. -/
theorem norm_minTensorIn_eq_spatialNorm (π₀ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ₀ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (hπ₀ : Function.Injective π₀)
    (hρ₀ : Function.Injective ρ₀) (x : A ⊗[ℂ] B) :
    ‖minTensorIn A B x‖
      = spatialNorm (StarRep.ofStarAlgHom π₀) (StarRep.ofStarAlgHom ρ₀) x := by
  rw [norm_minTensorIn, spatialNorm_eq_minTensorNorm π₀ ρ₀ hπ₀ hρ₀ x]

end Identification

end CStarTensor
end GroupApproximation
