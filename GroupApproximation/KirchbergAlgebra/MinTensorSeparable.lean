import GroupApproximation.Analysis.CStarMinTensorNorm
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Separability of the minimal tensor product

The minimal tensor product `A ⊗_min B` of separable C⋆-algebras is separable: the map
`(a, b) ↦ a ⊗ b` is a bounded bilinear map, so the elementary tensors form a separable set, their
`ℂ`-span contains the algebraic tensor product, and the algebraic tensor product is dense.

This is the separability conjunct of `IsKirchbergAlgebra (A ⊗_min B)`.
-/

namespace GroupApproximation
namespace KirchbergAlgebra

open CStarTensor
open scoped TensorProduct

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B] [Nontrivial A] [Nontrivial B]

/-- The elementary tensor map `A × B → A ⊗_min B` is continuous, by the cross-norm bound
`‖a ⊗ b‖ = ‖a‖ ‖b‖`. -/
theorem continuous_minTensorIn_tmul :
    Continuous fun p : A × B => minTensorIn A B (p.1 ⊗ₜ[ℂ] p.2) := by
  have hb : IsBoundedBilinearMap ℂ fun p : A × B => minTensorIn A B (p.1 ⊗ₜ[ℂ] p.2) :=
    { add_left := fun x₁ x₂ y => by simp only [TensorProduct.add_tmul, map_add]
      smul_left := fun c x y => by simp only [← TensorProduct.smul_tmul', map_smul]
      add_right := fun x y₁ y₂ => by simp only [TensorProduct.tmul_add, map_add]
      smul_right := fun c x y => by simp only [TensorProduct.tmul_smul, map_smul]
      bound := ⟨1, one_pos, fun x y => le_of_eq (by simp only [norm_minTensorIn_tmul, one_mul])⟩ }
  exact hb.continuous

/-- The image of the algebraic tensor product lies in the span of the elementary tensors. -/
theorem range_minTensorIn_subset_span :
    Set.range (minTensorIn A B) ⊆
      (Submodule.span ℂ (Set.range fun p : A × B => minTensorIn A B (p.1 ⊗ₜ[ℂ] p.2)) :
        Set (MinTensorProduct A B)) := by
  rintro _ ⟨x, rfl⟩
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | tmul a b => exact Submodule.subset_span ⟨(a, b), rfl⟩
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- **The minimal tensor product of separable C⋆-algebras is separable.** -/
theorem separableSpace_minTensorProduct [TopologicalSpace.SeparableSpace A]
    [TopologicalSpace.SeparableSpace B] :
    TopologicalSpace.SeparableSpace (MinTensorProduct A B) := by
  have hT : _root_.TopologicalSpace.IsSeparable
      (Set.range fun p : A × B => minTensorIn A B (p.1 ⊗ₜ[ℂ] p.2)) := by
    rw [← Set.image_univ]
    exact (_root_.TopologicalSpace.isSeparable_univ_iff.2 inferInstance).image
      continuous_minTensorIn_tmul
  have hS := _root_.TopologicalSpace.isSeparable_closure.2
    (_root_.TopologicalSpace.IsSeparable.span (R := ℂ) hT)
  refine _root_.TopologicalSpace.isSeparable_univ_iff.1 (hS.mono ?_)
  rw [← (denseRange_minTensorIn (A := A) (B := B)).closure_range]
  exact closure_mono range_minTensorIn_subset_span

end KirchbergAlgebra
end GroupApproximation
