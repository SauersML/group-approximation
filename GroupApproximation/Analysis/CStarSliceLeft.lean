import GroupApproximation.Analysis.CStarSliceCompletion

/-!
# The other slice

`CStarSliceBound` and `CStarSliceCompletion` build the slice that applies a
functional to the **left** leg and keeps the right one.  The exactness
sequence quotients the left leg, so the slice the exactness argument needs is
the other one: apply a functional to the right leg and keep the left.

Nothing here is new mathematics --- it is the same argument with the two legs
exchanged --- but the two legs are not interchangeable in the development,
because `spatialHom` and `minTensorNorm` are built from an ordered pair of
representations and no flip isometry exists yet.  So the mirror is written
out.

## Contents

* `sliceLeft` --- the algebraic second-variable slice, `a ⊗ b ↦ ψ b • a`;
* `inner_spatialHom_apply_left` --- the spatial matrix element read against
  it, the mirror of `inner_spatialHom_apply`;
* `norm_gnsRep_sliceLeft_le`, `norm_sliceLeft_vecFunctional_le` --- the
  analytic bound `‖sliceLeft (vecFunctional ψ η η') x‖ ≤ ‖η‖ ‖η'‖ ‖x‖_min`;
* `sliceLeftMin` --- the slice on `A ⊗_min B`, with its defining equation and
  its bound.

## Manuscript status

Infrastructure toward `SO.16`; certifies no manuscript step.
-/

namespace GroupApproximation
namespace CStarTensor

open CStarState
open scoped TensorProduct InnerProductSpace

noncomputable section

/-! ## The algebraic slice -/

section Algebraic

variable {V : Type u} {W : Type v} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- Slicing `V ⊗ W` in the **second** variable along a linear functional,
landing in `V`.  `coordSlice` is this map for a basis coordinate; the
exactness argument needs it for an arbitrary functional, because the
functionals it has are vector functionals of a representation and not
coordinates of a basis. -/
def sliceLeft (ψ : W →ₗ[ℂ] ℂ) : (V ⊗[ℂ] W) →ₗ[ℂ] V :=
  (TensorProduct.rid ℂ V).toLinearMap ∘ₗ LinearMap.lTensor V ψ

@[simp] theorem sliceLeft_tmul (ψ : W →ₗ[ℂ] ℂ) (a : V) (b : W) :
    sliceLeft ψ (a ⊗ₜ[ℂ] b) = ψ b • a := by
  simp only [sliceLeft, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul]

end Algebraic

/-! ## The spatial matrix element, read against the other slice -/

section Spatial

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
variable {H : Type w} {K : Type x} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K]
  [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- The mirror of `inner_spatialHom_apply`: the same matrix element, read as a
functional of the *second*-variable slice.  Both sides are
`⟪ξ', π a ξ⟫ * ⟪η', ρ b η⟫` on an elementary tensor. -/
theorem inner_spatialHom_apply_left (π : StarRep A H) (ρ : StarRep B K)
    (ξ ξ' : H) (η η' : K) (x : A ⊗[ℂ] B) :
    ⟪(ξ' ⊗ₜ[ℂ] η' : H ⊗[ℂ] K), spatialHom π ρ x (ξ ⊗ₜ[ℂ] η)⟫_ℂ
      = vecFunctional π ξ ξ' (sliceLeft (vecFunctional ρ η η') x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      rw [spatialHom_tmul, TensorProduct.mapL_tmul, TensorProduct.inner_tmul,
        sliceLeft_tmul]
      simp only [vecFunctional_apply, map_smul, smul_eq_mul]
      ring
  | add x y hx hy =>
      rw [map_add, add_apply, inner_add_right, hx, hy,
        map_add, map_add]

end Spatial

/-! ## The analytic bound -/

section Bound

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
  [Nontrivial A] [Nontrivial B]

/-- Each GNS representation of a second-variable vector-functional slice is
bounded by the minimal norm, scaled by the two vectors.  This is
`norm_gnsRep_sliceRight_le` with the legs exchanged. -/
theorem norm_gnsRep_sliceLeft_le (φ : State A) (ψ : State B)
    (η η' : ψ.GNSSpace) (x : A ⊗[ℂ] B) :
    ‖(φ.gnsRep).hom (sliceLeft (vecFunctional ψ.gnsRep η η') x)‖
      ≤ ‖η‖ * ‖η'‖ * minTensorNorm x := by
  set L := sliceLeft (vecFunctional ψ.gnsRep η η') x with hL
  set S := (φ.gnsRep).hom L with hS
  have hmin0 : 0 ≤ minTensorNorm x := by
    rw [minTensorNorm_apply]
    exact le_ciSup_of_le (bddAbove_spatialNorm_gnsRep x)
      ((φ, ψ) : State A × State B) (norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ξ ↦ ?_
  have hkey := inner_spatialHom_apply_left φ.gnsRep ψ.gnsRep ξ (S ξ) η η' x
  have hval : vecFunctional φ.gnsRep ξ (S ξ) L = ⟪S ξ, S ξ⟫_ℂ := rfl
  rw [hval] at hkey
  have hcs : ‖⟪((S ξ) ⊗ₜ[ℂ] η' : φ.GNSSpace ⊗[ℂ] ψ.GNSSpace),
        spatialHom φ.gnsRep ψ.gnsRep x (ξ ⊗ₜ[ℂ] η)⟫_ℂ‖
      ≤ (‖S ξ‖ * ‖η'‖)
        * ‖spatialHom φ.gnsRep ψ.gnsRep x (ξ ⊗ₜ[ℂ] η)‖ := by
    simpa [TensorProduct.norm_tmul] using norm_inner_le_norm (𝕜 := ℂ)
      ((S ξ) ⊗ₜ[ℂ] η' : φ.GNSSpace ⊗[ℂ] ψ.GNSSpace)
      (spatialHom φ.gnsRep ψ.gnsRep x (ξ ⊗ₜ[ℂ] η))
  have hop : ‖spatialHom φ.gnsRep ψ.gnsRep x (ξ ⊗ₜ[ℂ] η)‖
      ≤ ‖spatialHom φ.gnsRep ψ.gnsRep x‖ * (‖ξ‖ * ‖η‖) := by
    simpa [TensorProduct.norm_tmul] using
      ContinuousLinearMap.le_opNorm (spatialHom φ.gnsRep ψ.gnsRep x)
        (ξ ⊗ₜ[ℂ] η)
  have hsq : ‖S ξ‖ ^ 2 = ‖⟪S ξ, S ξ⟫_ℂ‖ := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    simp
  have hmin : ‖spatialHom φ.gnsRep ψ.gnsRep x‖ ≤ minTensorNorm x := by
    rw [minTensorNorm_apply]
    exact le_ciSup (bddAbove_spatialNorm_gnsRep x) ((φ, ψ) : State A × State B)
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

/-- **The analytic bound for the second-variable slice.** -/
theorem norm_sliceLeft_vecFunctional_le (ψ : State B) (η η' : ψ.GNSSpace)
    (x : A ⊗[ℂ] B) :
    ‖sliceLeft (vecFunctional ψ.gnsRep η η') x‖
      ≤ ‖η‖ * ‖η'‖ * minTensorNorm x := by
  obtain ⟨φ, hφ⟩ :=
    exists_state_norm_le_gnsRep (A := A)
      (sliceLeft (vecFunctional ψ.gnsRep η η') x)
  exact hφ.trans (norm_gnsRep_sliceLeft_le φ ψ η η' x)

/-- The bound restated against the norm of the canonical embedding, which is
the form `LinearMap.extendOfNorm` consumes. -/
theorem norm_sliceLeft_le_norm_minTensorInL (ψ : State B) (η η' : ψ.GNSSpace)
    (x : A ⊗[ℂ] B) :
    ‖sliceLeft (vecFunctional ψ.gnsRep η η') x‖
      ≤ (‖η‖ * ‖η'‖) * ‖minTensorInL A B x‖ := by
  rw [norm_minTensorInL]
  exact norm_sliceLeft_vecFunctional_le ψ η η' x

/-- **The second-variable slice on `A ⊗_min B`.** -/
def sliceLeftMin (ψ : State B) (η η' : ψ.GNSSpace) :
    MinTensorProduct A B →L[ℂ] A :=
  LinearMap.extendOfNorm (sliceLeft (vecFunctional ψ.gnsRep η η'))
    (minTensorInL A B)

@[simp] theorem sliceLeftMin_minTensorIn (ψ : State B) (η η' : ψ.GNSSpace)
    (x : A ⊗[ℂ] B) :
    sliceLeftMin (A := A) ψ η η' (minTensorIn A B x)
      = sliceLeft (vecFunctional ψ.gnsRep η η') x :=
  LinearMap.extendOfNorm_eq denseRange_minTensorInL
    ⟨‖η‖ * ‖η'‖, norm_sliceLeft_le_norm_minTensorInL ψ η η'⟩ x

theorem norm_sliceLeftMin_le (ψ : State B) (η η' : ψ.GNSSpace)
    (z : MinTensorProduct A B) :
    ‖sliceLeftMin (A := A) ψ η η' z‖ ≤ (‖η‖ * ‖η'‖) * ‖z‖ :=
  LinearMap.norm_extendOfNorm_apply_le denseRange_minTensorInL _
    (norm_sliceLeft_le_norm_minTensorInL ψ η η') z

end Bound

end

end CStarTensor
end GroupApproximation
