import GroupApproximation.Criterion.ChainConditionCompression
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Compression creates no invariant tensors of any finite type

`Criterion.ChainConditionCompression` proves that for a finite-dimensional
representation the fixed submodule of a compressed subgroup equals the
fixed submodule of the subgroup.  The manuscript applies that statement to
the representations induced on tensor constructions --- tensor products,
duals with the contragredient action, `Hom`-spaces, finite direct sums ---
and concludes that compression creates no invariant tensors of any finite
type, the commutant identity being the case `End(V) ≅ V ⊗ V*`.

The rigidity theorem is already universal over finite-dimensional
representations, so the mathematical content of that application is
precisely the *construction*: each tensor construction has to be given as
a representation of the same group, and each has to stay
finite-dimensional.  This file supplies the four constructions and reads
the corollary off.  Fixed types `V^{⊗p} ⊗ (V^*)^{⊗q}` are iterates of the
binary constructions, so they are covered by induction with no further
input.
-/

namespace GroupApproximation
namespace TensorInvariantRigidity

open scoped TensorProduct

universe u v

variable {G : Type u} [Group G] {k : Type v} [Field k]
variable {V W : Type v} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-! ## The induced representations -/

/-- The tensor product of two representations. -/
def tensorRep (σ : G →* (V ≃ₗ[k] V)) (τ : G →* (W ≃ₗ[k] W)) :
    G →* ((V ⊗[k] W) ≃ₗ[k] (V ⊗[k] W)) where
  toFun g := TensorProduct.congr (σ g) (τ g)
  map_one' := by
    refine LinearEquiv.toLinearMap_injective (TensorProduct.ext' ?_)
    intro x y
    simp
  map_mul' g h := by
    refine LinearEquiv.toLinearMap_injective (TensorProduct.ext' ?_)
    intro x y
    simp [LinearEquiv.mul_eq_trans]

@[simp] theorem tensorRep_apply_tmul (σ : G →* (V ≃ₗ[k] V))
    (τ : G →* (W ≃ₗ[k] W)) (g : G) (x : V) (y : W) :
    tensorRep σ τ g (x ⊗ₜ[k] y) = σ g x ⊗ₜ[k] τ g y := rfl

/-- The contragredient representation on the dual space.  The inverse is
what makes the contravariant `dualMap` into a left action. -/
def dualRep (σ : G →* (V ≃ₗ[k] V)) :
    G →* (Module.Dual k V ≃ₗ[k] Module.Dual k V) where
  toFun g := (σ g⁻¹).dualMap
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [LinearEquiv.mul_eq_trans]

/-- The representation on a `Hom`-space, by conjugation. -/
def homRep (σ : G →* (V ≃ₗ[k] V)) (τ : G →* (W ≃ₗ[k] W)) :
    G →* ((V →ₗ[k] W) ≃ₗ[k] (V →ₗ[k] W)) where
  toFun g := LinearEquiv.arrowCongr (σ g) (τ g)
  map_one' := by
    ext f x
    simp [LinearEquiv.one_eq_refl]
  map_mul' g h := by
    ext f x
    simp [LinearEquiv.mul_eq_trans]

/-- The direct sum of two representations. -/
def prodRep (σ : G →* (V ≃ₗ[k] V)) (τ : G →* (W ≃ₗ[k] W)) :
    G →* ((V × W) ≃ₗ[k] (V × W)) where
  toFun g := (σ g).prodCongr (τ g)
  map_one' := by
    ext x
    · simp
    · simp
  map_mul' g h := by
    ext x
    · simp [LinearEquiv.mul_eq_trans]
    · simp [LinearEquiv.mul_eq_trans]

/-! ## Compression is blind to every one of them -/

variable (σ : G →* (V ≃ₗ[k] V)) (τ : G →* (W ≃ₗ[k] W)) (Γ : Subgroup G) {t : G}

theorem tensor_fixedSubmodule_conjugate_eq [FiniteDimensional k V]
    [FiniteDimensional k W] (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) :
    fixedSubmodule (tensorRep σ τ)
        (Subgroup.map (MulAut.conj t).toMonoidHom Γ) =
      fixedSubmodule (tensorRep σ τ) Γ := by
  haveI : FiniteDimensional k (V ⊗[k] W) :=
    Module.Finite.of_basis ((Module.finBasis k V).tensorProduct (Module.finBasis k W))
  exact fixedSubmodule_conjugate_eq (tensorRep σ τ) Γ ht

theorem dual_fixedSubmodule_conjugate_eq [FiniteDimensional k V]
    (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) :
    fixedSubmodule (dualRep σ)
        (Subgroup.map (MulAut.conj t).toMonoidHom Γ) =
      fixedSubmodule (dualRep σ) Γ :=
  fixedSubmodule_conjugate_eq (dualRep σ) Γ ht

theorem hom_fixedSubmodule_conjugate_eq [FiniteDimensional k V]
    [FiniteDimensional k W] (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) :
    fixedSubmodule (homRep σ τ)
        (Subgroup.map (MulAut.conj t).toMonoidHom Γ) =
      fixedSubmodule (homRep σ τ) Γ := by
  exact fixedSubmodule_conjugate_eq (homRep σ τ) Γ ht

theorem prod_fixedSubmodule_conjugate_eq [FiniteDimensional k V]
    [FiniteDimensional k W] (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) :
    fixedSubmodule (prodRep σ τ)
        (Subgroup.map (MulAut.conj t).toMonoidHom Γ) =
      fixedSubmodule (prodRep σ τ) Γ :=
  fixedSubmodule_conjugate_eq (prodRep σ τ) Γ ht

/-- The mixed type `(1,1)`: invariant elements of `V ⊗ V*`, which is the
commutant identity `End(V) ≅ V ⊗ V*` of the manuscript. -/
theorem mixed_fixedSubmodule_conjugate_eq [FiniteDimensional k V]
    (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) :
    fixedSubmodule (tensorRep σ (dualRep σ))
        (Subgroup.map (MulAut.conj t).toMonoidHom Γ) =
      fixedSubmodule (tensorRep σ (dualRep σ)) Γ := by
  haveI : FiniteDimensional k (V ⊗[k] Module.Dual k V) :=
    Module.Finite.of_basis ((Module.finBasis k V).tensorProduct
      (Module.finBasis k (Module.Dual k V)))
  exact fixedSubmodule_conjugate_eq (tensorRep σ (dualRep σ)) Γ ht

/-- Closed form: on every tensor construction of a finite-dimensional
representation, a one-sided compression of a subgroup has exactly the
invariants the subgroup has. -/
theorem manuscriptTensorInvariantRigidity :
    ∀ {G : Type u} [Group G] {k V W : Type v} [Field k] [AddCommGroup V]
      [Module k V] [AddCommGroup W] [Module k W] [FiniteDimensional k V]
      [FiniteDimensional k W] (σ : G →* (V ≃ₗ[k] V))
      (τ : G →* (W ≃ₗ[k] W)) (Γ : Subgroup G) (t : G),
      (∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) →
        fixedSubmodule (tensorRep σ τ)
            (Subgroup.map (MulAut.conj t).toMonoidHom Γ) =
          fixedSubmodule (tensorRep σ τ) Γ ∧
        fixedSubmodule (dualRep σ)
            (Subgroup.map (MulAut.conj t).toMonoidHom Γ) =
          fixedSubmodule (dualRep σ) Γ ∧
        fixedSubmodule (homRep σ τ)
            (Subgroup.map (MulAut.conj t).toMonoidHom Γ) =
          fixedSubmodule (homRep σ τ) Γ ∧
        fixedSubmodule (prodRep σ τ)
            (Subgroup.map (MulAut.conj t).toMonoidHom Γ) =
          fixedSubmodule (prodRep σ τ) Γ := by
  intro G _ k V W _ _ _ _ _ _ _ σ τ Γ t ht
  exact ⟨tensor_fixedSubmodule_conjugate_eq σ τ Γ ht,
    dual_fixedSubmodule_conjugate_eq σ Γ ht,
    hom_fixedSubmodule_conjugate_eq σ τ Γ ht,
    prod_fixedSubmodule_conjugate_eq σ τ Γ ht⟩

end TensorInvariantRigidity
end GroupApproximation
