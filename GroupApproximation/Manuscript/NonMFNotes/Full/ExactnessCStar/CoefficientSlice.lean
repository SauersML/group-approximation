import GroupApproximation.Analysis.CStarExactnessSliceReduction
import GroupApproximation.Analysis.CStarExactComplex
import GroupApproximation.Analysis.CStarTakesakiIdentification

/-!
# Vector-functional slices of an arbitrary representation of the second leg

Source: `non_mf_group_notes.tex`, section `sec:Esofic`, paragraph
"Exactness": for a discrete group, group exactness gives exactness of the
reduced group C⋆-algebra \cite{KWExact}.  The argument reads the
coefficients of an element of `B ⊗_min C*_r(G)` through the vector
functionals `c ↦ ⟪δ_h, c δ₁⟫` of the regular representation, which are not
vector functionals of a GNS representation.  This file proves the slice
estimate for vector functionals of an *arbitrary* ⋆-representation of the
second leg on a complete Hilbert space, and its quotient form:

* `norm_sliceLeft_rep_le` ---
  `‖sliceLeft (vecFunctional ρ η η') x‖ ≤ ‖η‖ ‖η'‖ ‖x‖_min`;
* `norm_mk_sliceLeft_le` --- if `(q ⊗ id) z = 0`, the image in `B ⧸ I` of a
  slice of `x` is bounded by `‖η‖ ‖η'‖ ‖x - z‖_min`.
-/

namespace GroupApproximation.Full.NN09c

open GroupApproximation.CStarTensor GroupApproximation.CStarState
open scoped TensorProduct InnerProductSpace

universe u v w

section RepSlice

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]
variable {C : Type v} [CStarAlgebra C] [Nontrivial C]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

/-- Each GNS representation of the first leg bounds a vector-functional slice
of an arbitrary representation of the second leg by the minimal norm. -/
theorem norm_gnsRep_sliceLeft_rep_le (φ : State A) (ρ : StarRep C K)
    (η η' : K) (x : A ⊗[ℂ] C) :
    ‖(φ.gnsRep).hom (sliceLeft (vecFunctional ρ η η') x)‖
      ≤ ‖η‖ * ‖η'‖ * minTensorNorm x := by
  set L := sliceLeft (vecFunctional ρ η η') x
  set S := (φ.gnsRep).hom L
  have hmin : ‖spatialHom φ.gnsRep ρ x‖ ≤ minTensorNorm x := by
    have h := spatialNorm_le_minTensorNorm φ.gnsRep ρ x
    rwa [spatialNorm_apply] at h
  have hmin0 : 0 ≤ minTensorNorm x := (norm_nonneg _).trans hmin
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ξ ↦ ?_
  have hkey := inner_spatialHom_apply_left φ.gnsRep ρ ξ (S ξ) η η' x
  have hval : vecFunctional φ.gnsRep ξ (S ξ) L = ⟪S ξ, S ξ⟫_ℂ := rfl
  rw [hval] at hkey
  have hcs : ‖⟪((S ξ) ⊗ₜ[ℂ] η' : φ.GNSSpace ⊗[ℂ] K),
        spatialHom φ.gnsRep ρ x (ξ ⊗ₜ[ℂ] η)⟫_ℂ‖
      ≤ (‖S ξ‖ * ‖η'‖) * ‖spatialHom φ.gnsRep ρ x (ξ ⊗ₜ[ℂ] η)‖ := by
    simpa [TensorProduct.norm_tmul] using norm_inner_le_norm (𝕜 := ℂ)
      ((S ξ) ⊗ₜ[ℂ] η' : φ.GNSSpace ⊗[ℂ] K)
      (spatialHom φ.gnsRep ρ x (ξ ⊗ₜ[ℂ] η))
  have hop : ‖spatialHom φ.gnsRep ρ x (ξ ⊗ₜ[ℂ] η)‖
      ≤ ‖spatialHom φ.gnsRep ρ x‖ * (‖ξ‖ * ‖η‖) := by
    simpa [TensorProduct.norm_tmul] using
      ContinuousLinearMap.le_opNorm (spatialHom φ.gnsRep ρ x) (ξ ⊗ₜ[ℂ] η)
  have hsq : ‖S ξ‖ ^ 2 = ‖⟪S ξ, S ξ⟫_ℂ‖ := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    simp
  rcases eq_or_lt_of_le (norm_nonneg (S ξ)) with hz | hpos
  · rw [← hz]
    positivity
  · have hchain : ‖S ξ‖ ^ 2
        ≤ (‖S ξ‖ * ‖η'‖) * (minTensorNorm x * (‖ξ‖ * ‖η‖)) := by
      rw [hsq, ← hkey]
      refine hcs.trans ?_
      refine mul_le_mul_of_nonneg_left (hop.trans ?_) (by positivity)
      exact mul_le_mul_of_nonneg_right hmin (by positivity)
    nlinarith [norm_nonneg ξ, norm_nonneg η, norm_nonneg η', hmin0]

/-- **The slice estimate for an arbitrary representation of the second
leg**: `‖sliceLeft (vecFunctional ρ η η') x‖ ≤ ‖η‖ ‖η'‖ ‖x‖_min`. -/
theorem norm_sliceLeft_rep_le (ρ : StarRep C K) (η η' : K) (x : A ⊗[ℂ] C) :
    ‖sliceLeft (vecFunctional ρ η η') x‖ ≤ ‖η‖ * ‖η'‖ * minTensorNorm x := by
  obtain ⟨φ, hφ⟩ :=
    exists_state_norm_le_gnsRep (A := A) (sliceLeft (vecFunctional ρ η η') x)
  exact hφ.trans (norm_gnsRep_sliceLeft_rep_le φ ρ η η' x)

end RepSlice

section Quotient

variable {B : Type u} [CStarAlgebra B] [Nontrivial B]
variable {C : Type v} [CStarAlgebra C] [Nontrivial C]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]
variable (I : Ideal B) [I.IsTwoSided] [IsStarStable I] [IsClosed (I : Set B)]
  [Nontrivial (B ⧸ I)]

/-- **Slices of an approximant of a kernel element are almost in the ideal.**
If `(q ⊗ id) z = 0`, then for every algebraic tensor `x` the image in `B ⧸ I`
of a vector-functional slice of `x` has norm at most `‖η‖ ‖η'‖ ‖x - z‖_min`. -/
theorem norm_mk_sliceLeft_le (ρ : StarRep C K) (η η' : K) (x : B ⊗[ℂ] C)
    {z : MinTensorProduct B C} (hz : quotientMinTensorMap I z = 0) :
    ‖Ideal.Quotient.mk I (sliceLeft (vecFunctional ρ η η') x)‖
      ≤ ‖η‖ * ‖η'‖ * ‖minTensorIn B C x - z‖ := by
  have h1 : Ideal.Quotient.mk I (sliceLeft (vecFunctional ρ η η') x)
      = sliceLeft (vecFunctional ρ η η')
          (tensorStarAlgHomMap (C := C) (quotientStarMk I) x) := by
    rw [sliceLeft_tensorStarAlgHomMap, quotientStarMk_apply]
  have h2 : minTensorNorm (tensorStarAlgHomMap (C := C) (quotientStarMk I) x)
      = ‖quotientMinTensorMap I (minTensorIn B C x - z)‖ := by
    rw [map_sub, hz, sub_zero, quotientMinTensorMap_minTensorIn,
      norm_minTensorIn]
  rw [h1]
  refine (norm_sliceLeft_rep_le ρ η η' _).trans ?_
  rw [h2]
  exact mul_le_mul_of_nonneg_left (norm_quotientMinTensorMap_le I _)
    (by positivity)

end Quotient

end GroupApproximation.Full.NN09c
