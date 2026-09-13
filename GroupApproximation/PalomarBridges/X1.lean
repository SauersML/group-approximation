/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemXWitness
import Mathlib.Algebra.Algebra.Shrink

/-!
# Problem X(1) at universe zero

`NinetyNineProblems.amenableNonQuasidiagonalTrace` answers Problem X(1) of Schafhauser, Tikuisis
and White with a witness in `Type 1`, because the maximal group C⋆-algebra it uses lands there.
The Palomar statement `Palomar/STWProblemX1Challenge.lean` quantifies over `Type`, and this file
moves the witness down.

A separable metric space is `Small.{0}`, since the distances to a dense sequence separate points.
`TypeZeroModel A` is `Shrink.{0} A` with the norm and the star of `A` carried along the
equivalence. The equivalence is then a ⋆-isomorphism and an isometry, so `TypeZeroModel A` is a
separable C⋆-algebra. Amenable models pull back along the ⋆-isomorphism, and quasidiagonal models
pull back along its inverse, which is how non-quasidiagonality comes down.

The prose of this module was written by Claude (Anthropic).
-/

namespace GroupApproximation
namespace PalomarBridges
namespace X1

open Quasidiagonal

noncomputable section

universe u v

/-- A nonempty separable metric space is `Small.{0}`: the distances to a dense sequence give an
injection into `ℕ → ℝ`. -/
theorem small_zero_of_separableSpace (A : Type u) [MetricSpace A]
    [TopologicalSpace.SeparableSpace A] [Nonempty A] : Small.{0} A := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq A
  refine small_of_injective (β := ℕ → ℝ) (f := fun a n ↦ dist a (d n)) ?_
  intro a b hab
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  obtain ⟨n, hn⟩ := Metric.denseRange_iff.1 hd a (ε / 2) (half_pos hε)
  have h : dist a (d n) = dist b (d n) := congrFun hab n
  have htri := dist_triangle_right a b (d n)
  linarith

/-- A separable C⋆-algebra is `Small.{0}`. -/
theorem small_zero_of_cstarAlgebra (A : Type u) [CStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] : Small.{0} A :=
  haveI : Nonempty A := ⟨0⟩
  small_zero_of_separableSpace A

section Pullback

variable {A : Type u} [CStarAlgebra A] {B : Type v} [CStarAlgebra B]

/-- Amenable trace models pull back along a unital, multiplicative, `⋆`-preserving linear map.
The argument is the one for `QuasidiagonalTraceModel.comp`, with the Hilbert–Schmidt clause in
place of the operator-norm clause. -/
def amenableTraceModelComp {τ : B → ℂ} (M : AmenableTraceModel τ) (π : A →ₗ[ℂ] B)
    (hone : π 1 = 1) (hmul : ∀ x y : A, π (x * y) = π x * π y)
    (hstar : ∀ x : A, π (star x) = star (π x)) :
    AmenableTraceModel (fun x : A ↦ τ (π x)) where
  space := M.space
  map n := (M.map n).comp π
  map_one n := by
    simp only [LinearMap.comp_apply, hone]
    exact M.map_one n
  completelyPositive n := by
    intro m a w
    have hrw : ∀ i j : Fin m, π (star (a i) * a j) = star (π (a i)) * π (a j) :=
      fun i j ↦ by rw [hmul, hstar]
    simpa only [LinearMap.comp_apply, hrw] using
      M.completelyPositive n m (fun i ↦ π (a i)) w
  tendsto_mul_hs x y := by
    simpa only [LinearMap.comp_apply, hmul] using M.tendsto_mul_hs (π x) (π y)
  tendsto_trace x := by
    simpa only [LinearMap.comp_apply] using M.tendsto_trace (π x)

/-- Amenability of a trace pulls back along a unital `⋆`-homomorphism. -/
theorem isAmenableTrace_comp {τ : B → ℂ} (h : IsAmenableTrace τ) (π : A →⋆ₐ[ℂ] B) :
    IsAmenableTrace (fun x : A ↦ τ (π x)) := by
  obtain ⟨M⟩ := h
  exact ⟨amenableTraceModelComp M π.toAlgHom.toLinearMap (by simp) (fun x y ↦ by simp)
    (fun x ↦ map_star π x)⟩

end Pullback

section TypeZero

attribute [local instance] small_zero_of_cstarAlgebra

variable (A : Type u) [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]

/-- A separable C⋆-algebra, moved to `Type`. -/
def TypeZeroModel : Type :=
  Shrink.{0} A

instance : Ring (TypeZeroModel A) :=
  inferInstanceAs (Ring (Shrink.{0} A))

instance : Algebra ℂ (TypeZeroModel A) :=
  inferInstanceAs (Algebra ℂ (Shrink.{0} A))

/-- The algebra isomorphism `TypeZeroModel A ≃ₐ[ℂ] A`. -/
def typeZeroAlgEquiv : TypeZeroModel A ≃ₐ[ℂ] A :=
  Shrink.algEquiv ℂ A

instance : NormedRing (TypeZeroModel A) :=
  NormedRing.induced (TypeZeroModel A) A (typeZeroAlgEquiv A) (typeZeroAlgEquiv A).injective

instance : NormedAlgebra ℂ (TypeZeroModel A) where
  toAlgebra := inferInstance
  norm_smul_le r x := by
    show ‖typeZeroAlgEquiv A (r • x)‖ ≤ ‖r‖ * ‖typeZeroAlgEquiv A x‖
    rw [map_smul]
    exact norm_smul_le r _

instance : Star (TypeZeroModel A) where
  star x := (typeZeroAlgEquiv A).symm (star (typeZeroAlgEquiv A x))

theorem typeZeroAlgEquiv_star (x : TypeZeroModel A) :
    typeZeroAlgEquiv A (star x) = star (typeZeroAlgEquiv A x) :=
  (typeZeroAlgEquiv A).apply_symm_apply _

instance : StarRing (TypeZeroModel A) where
  star_involutive x := (typeZeroAlgEquiv A).injective <| by
    simp only [typeZeroAlgEquiv_star, star_star]
  star_mul x y := (typeZeroAlgEquiv A).injective <| by
    simp only [typeZeroAlgEquiv_star, map_mul, star_mul]
  star_add x y := (typeZeroAlgEquiv A).injective <| by
    simp only [typeZeroAlgEquiv_star, map_add, star_add]

instance : StarModule ℂ (TypeZeroModel A) where
  star_smul r x := (typeZeroAlgEquiv A).injective <| by
    simp only [typeZeroAlgEquiv_star, map_smul, star_smul]

instance : CStarRing (TypeZeroModel A) where
  norm_mul_self_le x := by
    show ‖typeZeroAlgEquiv A x‖ * ‖typeZeroAlgEquiv A x‖ ≤ ‖typeZeroAlgEquiv A (star x * x)‖
    rw [map_mul, typeZeroAlgEquiv_star]
    exact CStarRing.norm_mul_self_le _

/-- The equivalence is an isometry for the transported norm. -/
def typeZeroIsometryEquiv : TypeZeroModel A ≃ᵢ A where
  toEquiv := (typeZeroAlgEquiv A).toEquiv
  isometry_toFun := AddMonoidHomClass.isometry_of_norm (typeZeroAlgEquiv A) fun _ ↦ rfl

instance : CompleteSpace (TypeZeroModel A) :=
  (typeZeroIsometryEquiv A).completeSpace

instance : CStarAlgebra (TypeZeroModel A) where

instance : TopologicalSpace.SeparableSpace (TypeZeroModel A) :=
  (typeZeroIsometryEquiv A).symm.surjective.denseRange.separableSpace
    (typeZeroIsometryEquiv A).symm.continuous

/-- The unital `⋆`-homomorphism `TypeZeroModel A → A`. -/
def typeZeroStarAlgHom : TypeZeroModel A →⋆ₐ[ℂ] A where
  toAlgHom := (typeZeroAlgEquiv A).toAlgHom
  map_star' := typeZeroAlgEquiv_star A

/-- The unital `⋆`-homomorphism `A → TypeZeroModel A`. -/
def typeZeroSymmStarAlgHom : A →⋆ₐ[ℂ] TypeZeroModel A where
  toAlgHom := (typeZeroAlgEquiv A).symm.toAlgHom
  map_star' x := (typeZeroAlgEquiv A).injective <| by
    show typeZeroAlgEquiv A ((typeZeroAlgEquiv A).symm (star x))
      = typeZeroAlgEquiv A (star ((typeZeroAlgEquiv A).symm x))
    simp only [typeZeroAlgEquiv_star, AlgEquiv.apply_symm_apply]

end TypeZero

open NinetyNineProblems in
/-- **Problem X(1) fails at universe zero**: some separable C⋆-algebra in `Type` carries a
tracial state that is amenable and not quasidiagonal. -/
theorem amenableNonQuasidiagonalTrace_zero : AmenableNonQuasidiagonalTrace.{0} := by
  obtain ⟨A, _inst, τ, _hsep, hamen, hnot⟩ := amenableNonQuasidiagonalTrace
  refine ⟨TypeZeroModel A, inferInstance, τ.compStarAlgHom (typeZeroStarAlgHom A), inferInstance,
    isAmenableTrace_comp hamen (typeZeroStarAlgHom A), fun hqd ↦ hnot ?_⟩
  have h := hqd.comp (typeZeroSymmStarAlgHom A)
  have hfun : (fun x : A ↦ (τ.compStarAlgHom (typeZeroStarAlgHom A))
      (typeZeroSymmStarAlgHom A x)) = fun a : A ↦ τ a :=
    funext fun x ↦ congrArg τ.toLinearMap ((typeZeroAlgEquiv A).apply_symm_apply x)
  rw [← hfun]
  exact h

end

end X1
end PalomarBridges
end GroupApproximation
