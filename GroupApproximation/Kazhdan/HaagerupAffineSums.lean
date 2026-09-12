import GroupApproximation.Kazhdan.HaagerupUnion
import GroupApproximation.Kazhdan.TreeHalfSpaces
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite sums of affine actions, trees, and homomorphisms to `ℤ`

The action step of "every countable subgroup of `GL_2` over a field has the Haagerup property"
(`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring`, tex lines 1146--1147).
A finitely generated subgroup of `GL_2` acts on finitely many Bruhat--Tits trees and has finitely
many determinant valuations; the sum of the corresponding affine actions is proper when the joint
displacement is.  This module provides the three ingredients with no literature input.

* **Finite sums** (`AffineAction.sum`, `hasHaagerupProperty_of_finite_sum`): the `ℓ²`-sum of a
  finite family of affine isometric actions is an affine isometric action whose translation part
  dominates every summand, so it is proper as soon as `{g : ‖b_i g‖ ≤ R for all i}` is finite.
* **Trees** (`treeAction`): a group acting on a tree by graph automorphisms acts on `ℓ²` of the
  darts through the half-space cocycle `g ↦ c(x₀, g x₀)`, and `d(x₀, g x₀) ≤ ‖c(x₀, g x₀)‖²`
  (`dist_le_norm_sq_treeAction`).
* **Homomorphisms to `ℤ`** (`intAction`): translation of the real line.
-/

namespace GroupApproximation
namespace Haagerup

open Delorme
open scoped ENNReal

universe u v

/-- An affine isometric action of a discrete group on a complete real inner product space, not
required to be proper. -/
structure AffineAction (G : Type u) [Group G] where
  /-- The Hilbert space acted on. -/
  E : Type v
  [normed : NormedAddCommGroup E]
  [inner : InnerProductSpace ℝ E]
  [complete : CompleteSpace E]
  /-- The linear part of the action. -/
  π : G →* (E ≃ₗᵢ[ℝ] E)
  /-- The translation part of the action. -/
  b : G → E
  isCocycle : IsCocycle π b

attribute [instance] AffineAction.normed AffineAction.inner AffineAction.complete

namespace AffineAction

variable {G : Type u} [Group G]

/-- The `ℓ²`-sum of a finite family of affine actions. -/
noncomputable def sum {ι : Type} [Finite ι] (A : ι → AffineAction.{u, v} G) :
    AffineAction.{u, v} G where
  E := lp (fun i ↦ (A i).E) 2
  π := lpRepresentation fun i ↦ (A i).π
  b g := ⟨fun i ↦ (A i).b g, Memℓp.all _⟩
  isCocycle g h := by
    apply lp.ext
    funext i
    rw [lp.coeFn_add, Pi.add_apply]
    exact (A i).isCocycle g h

theorem norm_b_le_norm_sum_b {ι : Type} [Finite ι] (A : ι → AffineAction.{u, v} G) (g : G)
    (i : ι) : ‖(A i).b g‖ ≤ ‖(sum A).b g‖ :=
  lp.norm_apply_le_norm (E := fun i ↦ (A i).E) (p := 2) (by norm_num)
    (⟨fun i ↦ (A i).b g, Memℓp.all _⟩ : lp (fun i ↦ (A i).E) 2) i

end AffineAction

/-- **Finite sums of affine actions.**  If the joint displacement is proper, the `ℓ²`-sum is a
metrically proper affine isometric action. -/
theorem hasHaagerupProperty_of_finite_sum {G : Type u} [Group G] {ι : Type} [Finite ι]
    (A : ι → AffineAction.{u, v} G)
    (hproper : ∀ R : ℝ, {g : G | ∀ i, ‖(A i).b g‖ ≤ R}.Finite) :
    HasHaagerupProperty.{u, v} G :=
  ⟨{ E := (AffineAction.sum A).E
     π := (AffineAction.sum A).π
     b := (AffineAction.sum A).b
     isCocycle := (AffineAction.sum A).isCocycle
     proper := fun R ↦ (hproper R).subset fun g hg i ↦
       (AffineAction.norm_b_le_norm_sum_b A g i).trans hg }⟩

/-! ## Trees -/

section Tree

variable {G V : Type u} [Group G] [MulAction G V] {H : SimpleGraph V}

/-- The half-space affine action of a group acting on a tree. -/
noncomputable def treeAction (hT : H.IsTree) (hG : TreeAction.IsGraphAction G H) (x₀ : V) :
    AffineAction.{u, u} G := by
  letI := TreeAction.dartSMul hG
  exact
    { E := lp (fun _ : H.Dart ↦ ℝ) 2
      π := KazhdanFiniteGeneration.permutationRepresentation G H.Dart
      b := fun g ↦ (TreeAction.treeHalfSpaces hT hG).sepVec x₀ (g • x₀)
      isCocycle := (TreeAction.treeHalfSpaces hT hG).isCocycle_orbit x₀ }

/-- The displacement on the tree is at most the squared norm of the half-space cocycle. -/
theorem dist_le_norm_sq_treeAction (hT : H.IsTree) (hG : TreeAction.IsGraphAction G H) (x₀ : V)
    (g : G) : (H.dist x₀ (g • x₀) : ℝ) ≤ ‖(treeAction hT hG x₀).b g‖ ^ 2 := by
  letI := TreeAction.dartSMul hG
  have h1 : (H.dist x₀ (g • x₀) : ℝ) ≤
      ((TreeAction.treeHalfSpaces hT hG).sepFinset x₀ (g • x₀)).card :=
    Nat.cast_le.mpr (TreeAction.dist_le_card_sepFinset hT hG x₀ (g • x₀))
  have h2 := (TreeAction.treeHalfSpaces hT hG).card_sepFinset_le_norm_rpow x₀ (g • x₀)
  have e2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [e2, Real.rpow_two] at h2
  exact h1.trans h2

end Tree

/-! ## Homomorphisms to `ℤ` -/

/-- The translation action on the real line of a homomorphism to `ℤ`. -/
noncomputable def intAction {G : Type u} [Group G] (f : G →* Multiplicative ℤ) :
    AffineAction.{u, 0} G where
  E := ℝ
  π := 1
  b g := (Multiplicative.toAdd (f g) : ℝ)
  isCocycle g h := by
    have e : Multiplicative.toAdd (f (g * h)) =
        Multiplicative.toAdd (f g) + Multiplicative.toAdd (f h) := by
      rw [map_mul, toAdd_mul]
    show ((Multiplicative.toAdd (f (g * h)) : ℤ) : ℝ) =
      (Multiplicative.toAdd (f g) : ℝ) + (Multiplicative.toAdd (f h) : ℝ)
    rw [e, Int.cast_add]

theorem norm_intAction_b {G : Type u} [Group G] (f : G →* Multiplicative ℤ) (g : G) :
    ‖(intAction f).b g‖ = |(Multiplicative.toAdd (f g) : ℝ)| :=
  Real.norm_eq_abs _

end Haagerup
end GroupApproximation

#audit_axioms GroupApproximation.Haagerup.hasHaagerupProperty_of_finite_sum
#audit_axioms GroupApproximation.Haagerup.dist_le_norm_sq_treeAction
