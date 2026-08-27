import GroupApproximation.Analysis.CStarMinTensorNorm

/-!
# The analytic slice bound

Toward proof-ledger row `SO.16`.  The Fubini identity that stands between
`CStarMinTensorInjective` and the Kirchberg--Wassermann crossover needs the
slice maps to survive the passage from the algebraic tensor product to the
minimal completion, and that is an estimate: a slice must be bounded by the
minimal norm.

The algebraic vocabulary is already in place --- `sliceRight` and
`coordSlice` in `Analysis/CStarTensorProductSpatial`, with
`coord_sliceRight` --- and `CStarMinTensorNorm` runs it, its faithfulness
argument being the degenerate case of Fubini.  What was missing is the
estimate, and this module supplies it for the vector functionals, which are
the case the Fubini argument uses because they separate.

## The argument

`inner_spatialHom_apply` already writes a spatial matrix element of `x` as an
inner product against a slice:

`⟪ξ' ⊗ η', spatialHom π ρ x (ξ ⊗ η)⟫ = ⟪η', ρ (R x) η⟫`,
  `R x := sliceRight (vecFunctional π ξ ξ') x`.

Take `η' := ρ (R x) η`.  The left side is bounded by
`‖ξ'‖ * ‖ρ (R x) η‖ * ‖spatialHom π ρ x‖ * ‖ξ‖ * ‖η‖` by Cauchy--Schwarz and
`TensorProduct.norm_tmul`, the right side is `‖ρ (R x) η‖²`, and one factor of
`‖ρ (R x) η‖` cancels.  So every GNS representation of `R x` is bounded by
`‖ξ‖ * ‖ξ'‖ * ‖x‖_min`, and `exists_state_norm_le_gnsRep` turns that into a
bound on `‖R x‖` itself, because the GNS family attains every norm.

## Manuscript status

Infrastructure toward `SO.16`; certifies no manuscript step.  The Fubini
identity itself is still not proved.
-/

namespace GroupApproximation
namespace CStarTensor

open CStarState
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
  [Nontrivial A] [Nontrivial B]

/-- Each GNS representation of a vector-functional slice is bounded by the
minimal norm, scaled by the two vectors. -/
theorem norm_gnsRep_sliceRight_le (φ : State A) (ξ ξ' : φ.GNSSpace)
    (ψ : State B) (x : A ⊗[ℂ] B) :
    ‖(ψ.gnsRep).hom (sliceRight (vecFunctional φ.gnsRep ξ ξ') x)‖
      ≤ ‖ξ‖ * ‖ξ'‖ * minTensorNorm x := by
  set R := sliceRight (vecFunctional φ.gnsRep ξ ξ') x with hR
  set T := (ψ.gnsRep).hom R with hT
  -- the minimal norm is a supremum of seminorms, hence nonnegative
  have hmin0 : 0 ≤ minTensorNorm x := by
    rw [minTensorNorm_apply]
    exact le_ciSup_of_le (bddAbove_spatialNorm_gnsRep x)
      ((φ, ψ) : State A × State B) (norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun η ↦ ?_
  -- the spatial matrix element, read against the slice
  have hkey := inner_spatialHom_apply φ.gnsRep ψ.gnsRep ξ ξ' η (T η) x
  have hval : vecFunctional ψ.gnsRep η (T η) R = ⟪T η, T η⟫_ℂ := rfl
  rw [hval] at hkey
  -- Cauchy--Schwarz on the left, with the tensor norms split
  have hcs : ‖⟪(ξ' ⊗ₜ[ℂ] (T η) : φ.GNSSpace ⊗[ℂ] ψ.GNSSpace),
        spatialHom φ.gnsRep ψ.gnsRep x (ξ ⊗ₜ[ℂ] η)⟫_ℂ‖
      ≤ (‖ξ'‖ * ‖T η‖)
        * ‖spatialHom φ.gnsRep ψ.gnsRep x (ξ ⊗ₜ[ℂ] η)‖ := by
    simpa [TensorProduct.norm_tmul] using norm_inner_le_norm (𝕜 := ℂ)
      (ξ' ⊗ₜ[ℂ] (T η) : φ.GNSSpace ⊗[ℂ] ψ.GNSSpace)
      (spatialHom φ.gnsRep ψ.gnsRep x (ξ ⊗ₜ[ℂ] η))
  have hop : ‖spatialHom φ.gnsRep ψ.gnsRep x (ξ ⊗ₜ[ℂ] η)‖
      ≤ ‖spatialHom φ.gnsRep ψ.gnsRep x‖ * (‖ξ‖ * ‖η‖) := by
    simpa [TensorProduct.norm_tmul] using
      ContinuousLinearMap.le_opNorm (spatialHom φ.gnsRep ψ.gnsRep x)
        (ξ ⊗ₜ[ℂ] η)
  have hsq : ‖T η‖ ^ 2 = ‖⟪T η, T η⟫_ℂ‖ := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    simp
  -- the spatial norm is at most the minimal norm
  have hmin : ‖spatialHom φ.gnsRep ψ.gnsRep x‖ ≤ minTensorNorm x := by
    rw [minTensorNorm_apply]
    exact le_ciSup (bddAbove_spatialNorm_gnsRep x) ((φ, ψ) : State A × State B)
  -- assemble and cancel one factor of `‖T η‖`
  rcases eq_or_lt_of_le (norm_nonneg (T η)) with hz | hpos
  · rw [← hz]
    positivity
  · have hchain : ‖T η‖ ^ 2
        ≤ (‖ξ'‖ * ‖T η‖) * (minTensorNorm x * (‖ξ‖ * ‖η‖)) := by
      rw [hsq, ← hkey]
      refine hcs.trans ?_
      refine mul_le_mul_of_nonneg_left (hop.trans ?_) (by positivity)
      exact mul_le_mul_of_nonneg_right hmin (by positivity)
    nlinarith [norm_nonneg ξ, norm_nonneg ξ', norm_nonneg η, hmin0]

/-- **The analytic slice bound**, for a vector functional: the slice of `x` is
bounded by the minimal tensor norm of `x`, scaled by the two vectors.  This is
what carries `sliceRight` from the algebraic tensor product to the minimal
completion. -/
theorem norm_sliceRight_vecFunctional_le (φ : State A) (ξ ξ' : φ.GNSSpace)
    (x : A ⊗[ℂ] B) :
    ‖sliceRight (vecFunctional φ.gnsRep ξ ξ') x‖
      ≤ ‖ξ‖ * ‖ξ'‖ * minTensorNorm x := by
  obtain ⟨ψ, hψ⟩ :=
    exists_state_norm_le_gnsRep (sliceRight (vecFunctional φ.gnsRep ξ ξ') x)
  exact hψ.trans (norm_gnsRep_sliceRight_le φ ξ ξ' ψ x)

end

end CStarTensor
end GroupApproximation
