import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# The point-norm topology on `Aut(A)`

For a unital C*-algebra `A`, `PointNormAut A` is the automorphism group `A ≃⋆ₐ[ℂ] A` with the
point-norm topology: `α_i → α` when `α_i a → α a` in norm for every `a : A` (STW, footnote 101).
Automorphisms of C*-algebras are isometries, so evaluation is jointly continuous and the
point-norm topology is a group topology.

## Main declarations

* `GroupApproximation.AutLoops.PointNormAut`: the type synonym, with the group `StarAlgEquiv.aut`.
* `PointNormAut.continuous_iff`: continuity into `PointNormAut A` is pointwise continuity.
* `PointNormAut.continuous_apply₂`: `x ↦ f x (g x)` is continuous for continuous `f` and `g`.
* `PointNormAut.instIsTopologicalGroup`: `PointNormAut A` is a topological group.
-/

open Filter Topology

namespace GroupApproximation
namespace AutLoops

/-- The automorphism group `Aut(A)` of a unital C*-algebra with the point-norm topology. -/
def PointNormAut (A : Type*) [CStarAlgebra A] : Type _ := A ≃⋆ₐ[ℂ] A

namespace PointNormAut

variable {A : Type*} [CStarAlgebra A]

instance : Group (PointNormAut A) := StarAlgEquiv.aut

instance : FunLike (PointNormAut A) A A := inferInstanceAs (FunLike (A ≃⋆ₐ[ℂ] A) A A)

/-- The underlying automorphism. -/
def toAut (α : PointNormAut A) : A ≃⋆ₐ[ℂ] A := α

/-- An automorphism as a point of `PointNormAut A`. -/
def ofAut (α : A ≃⋆ₐ[ℂ] A) : PointNormAut A := α

@[simp] theorem coe_toAut (α : PointNormAut A) : ⇑(toAut α) = ⇑α := rfl

@[simp] theorem coe_ofAut (α : A ≃⋆ₐ[ℂ] A) : ⇑(ofAut α) = ⇑α := rfl

@[simp] theorem mul_apply (α β : PointNormAut A) (a : A) : (α * β) a = α (β a) := rfl

@[simp] theorem one_apply (a : A) : (1 : PointNormAut A) a = a := rfl

theorem apply_inv_apply (α : PointNormAut A) (a : A) : α (α⁻¹ a) = a :=
  (toAut α).apply_symm_apply a

theorem inv_apply_apply (α : PointNormAut A) (a : A) : α⁻¹ (α a) = a :=
  (toAut α).symm_apply_apply a

theorem map_sub (α : PointNormAut A) (a b : A) : α (a - b) = α a - α b :=
  _root_.map_sub (toAut α) a b

theorem map_mul (α : PointNormAut A) (a b : A) : α (a * b) = α a * α b :=
  _root_.map_mul (toAut α) a b

theorem map_one (α : PointNormAut A) : α 1 = 1 :=
  _root_.map_one (toAut α)

theorem map_star (α : PointNormAut A) (a : A) : α (star a) = star (α a) :=
  StarHomClass.map_star (toAut α) a

/-- Automorphisms of a C*-algebra are isometric. -/
theorem norm_apply (α : PointNormAut A) (a : A) : ‖α a‖ = ‖a‖ :=
  StarAlgEquiv.norm_map (toAut α) a

/-- The point-norm topology, induced by `α ↦ ⇑α` into the product topology on `A → A`. -/
instance : TopologicalSpace (PointNormAut A) :=
  TopologicalSpace.induced (fun α : PointNormAut A => (α : A → A)) inferInstance

theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → PointNormAut A} :
    Continuous f ↔ ∀ a, Continuous fun x => f x a :=
  continuous_induced_rng.trans continuous_pi_iff

theorem continuous_apply (a : A) : Continuous fun α : PointNormAut A => α a :=
  continuous_iff.1 continuous_id a

/-- Evaluation is jointly continuous for the point-norm topology. -/
theorem continuous_apply₂ {X : Type*} [TopologicalSpace X] {f : X → PointNormAut A} {g : X → A}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x (g x) := by
  refine continuous_iff_continuousAt.2 fun x₀ => tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have h₁ : Tendsto (fun x => ‖g x - g x₀‖) (𝓝 x₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (hg.tendsto x₀)
  have h₂ : Tendsto (fun x => ‖f x (g x₀) - f x₀ (g x₀)‖) (𝓝 x₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 ((continuous_iff.1 hf (g x₀)).tendsto x₀)
  have h₃ : Tendsto (fun x => ‖g x - g x₀‖ + ‖f x (g x₀) - f x₀ (g x₀)‖) (𝓝 x₀) (𝓝 0) := by
    simpa only [add_zero] using h₁.add h₂
  refine squeeze_zero (fun _ => norm_nonneg _) (fun x => ?_) h₃
  calc ‖f x (g x) - f x₀ (g x₀)‖
      = ‖f x (g x - g x₀) + (f x (g x₀) - f x₀ (g x₀))‖ := by
        rw [map_sub, sub_add_sub_cancel]
    _ ≤ ‖f x (g x - g x₀)‖ + ‖f x (g x₀) - f x₀ (g x₀)‖ := norm_add_le _ _
    _ = ‖g x - g x₀‖ + ‖f x (g x₀) - f x₀ (g x₀)‖ := by rw [norm_apply]

instance : ContinuousMul (PointNormAut A) where
  continuous_mul := continuous_iff.2 fun a =>
    continuous_apply₂ (f := Prod.fst) (g := fun x : PointNormAut A × PointNormAut A => x.2 a)
      continuous_fst ((continuous_apply a).comp continuous_snd)

instance : ContinuousInv (PointNormAut A) where
  continuous_inv := by
    refine continuous_iff.2 fun a => continuous_iff_continuousAt.2 fun α₀ => ?_
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    refine (tendsto_iff_norm_sub_tendsto_zero.1
      ((continuous_apply (α₀⁻¹ a)).tendsto α₀)).congr fun α => ?_
    calc ‖α (α₀⁻¹ a) - α₀ (α₀⁻¹ a)‖ = ‖α (α₀⁻¹ a - α⁻¹ a)‖ := by
          rw [map_sub, apply_inv_apply, apply_inv_apply]
      _ = ‖α⁻¹ a - α₀⁻¹ a‖ := by rw [norm_apply, norm_sub_rev]

instance instIsTopologicalGroup : IsTopologicalGroup (PointNormAut A) where

end PointNormAut

end AutLoops
end GroupApproximation
