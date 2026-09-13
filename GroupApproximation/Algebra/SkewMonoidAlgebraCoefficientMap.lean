import GroupApproximation.Pestov91.CrossedProduct
import GroupApproximation.Meta.AxiomGuard

/-!
# Coefficient maps of skew monoid algebras

`non_mf_groups_exist.tex`, line 1437 (proof of `lem:chain-core-models`, general `X`):
"Coefficient pullback gives injective unital maps of crossed products, and every locally
constant function is constant on a sufficiently fine partition."

An equivariant ring homomorphism `φ : A →+* B` induces the ring homomorphism
`coeffMap φ hφ : A ⋊ G →+* B ⋊ G`, `single g a ↦ single g (φ a)`.  It is unital, and it is
injective or surjective when `φ` is.  Pulling locally constant functions back along a factor map
gives such a `φ`; so does restricting them to a closed invariant subset.

* `coeffMap`, `coeffMap_apply`, `coeffMap_single`, `coeff_coeffMap`, `coeffMap_C`;
* `coeffMap_injective`, `coeffMap_surjective`.
-/

namespace GroupApproximation
namespace Pestov91
namespace CrossedProduct

open SkewMonoidAlgebra (single)

section Monoid

variable {G : Type*} [Monoid G] {A B : Type*} [Ring A] [Ring B]
  [MulSemiringAction G A] [MulSemiringAction G B]
  (φ : A →+* B) (hφ : ∀ (g : G) (a : A), φ (g • a) = g • φ a)

/-- The ring homomorphism `A ⋊ G →+* B ⋊ G` induced by an equivariant ring homomorphism
`φ : A →+* B`: `single g a ↦ single g (φ a)`. -/
noncomputable def coeffMap : SkewMonoidAlgebra A G →+* SkewMonoidAlgebra B G :=
  SkewMonoidAlgebra.liftNCRingHom
    ((SkewMonoidAlgebra.singleOneRingHom : B →+* SkewMonoidAlgebra B G).comp φ)
    (SkewMonoidAlgebra.of B G) fun {x y} ↦ by
      show single 1 (φ (y • x)) * single y 1 = single y 1 * single 1 (φ x)
      rw [SkewMonoidAlgebra.single_mul_single, SkewMonoidAlgebra.single_mul_single, hφ, one_mul,
        smul_one, mul_one, mul_one, one_mul]

theorem coeffMap_apply (x : SkewMonoidAlgebra A G) :
    coeffMap φ hφ x = SkewMonoidAlgebra.liftNC
      (((SkewMonoidAlgebra.singleOneRingHom : B →+* SkewMonoidAlgebra B G).comp φ :
        A →+* SkewMonoidAlgebra B G) : A →+ SkewMonoidAlgebra B G)
      (SkewMonoidAlgebra.of B G) x :=
  rfl

@[simp]
theorem coeffMap_single (g : G) (a : A) : coeffMap φ hφ (single g a) = single g (φ a) := by
  rw [coeffMap_apply, SkewMonoidAlgebra.liftNC_single]
  show single 1 (φ a) * single g 1 = single g (φ a)
  rw [SkewMonoidAlgebra.single_mul_single, one_mul, smul_one, mul_one]

theorem coeff_coeffMap (x : SkewMonoidAlgebra A G) (g : G) :
    (coeffMap φ hφ x).coeff g = φ (x.coeff g) := by
  classical
  induction x using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | single h a =>
    rw [coeffMap_single, SkewMonoidAlgebra.coeff_single_apply,
      SkewMonoidAlgebra.coeff_single_apply]
    split_ifs <;> simp
  | add x y hx hy => simp [hx, hy]

/-- Coefficient maps along injective equivariant homomorphisms are injective. -/
theorem coeffMap_injective (hinj : Function.Injective φ) : Function.Injective (coeffMap φ hφ) := by
  intro x y hxy
  refine SkewMonoidAlgebra.ext fun g ↦ hinj ?_
  rw [← coeff_coeffMap φ hφ x g, ← coeff_coeffMap φ hφ y g, hxy]

/-- Coefficient maps along surjective equivariant homomorphisms are surjective. -/
theorem coeffMap_surjective (hsurj : Function.Surjective φ) :
    Function.Surjective (coeffMap φ hφ) := by
  intro y
  induction y using SkewMonoidAlgebra.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | single g b =>
    obtain ⟨a, rfl⟩ := hsurj b
    exact ⟨single g a, coeffMap_single φ hφ g a⟩
  | add y z hy hz =>
    obtain ⟨y', rfl⟩ := hy
    obtain ⟨z', rfl⟩ := hz
    exact ⟨y' + z', map_add _ _ _⟩

end Monoid

section Int

variable {A B : Type*} [Ring A] [Ring B]
  [MulSemiringAction (Multiplicative ℤ) A] [MulSemiringAction (Multiplicative ℤ) B]
  (φ : A →+* B) (hφ : ∀ (g : Multiplicative ℤ) (a : A), φ (g • a) = g • φ a)

@[simp]
theorem coeffMap_C (a : A) : coeffMap φ hφ (C a) = C (φ a) :=
  coeffMap_single φ hφ 1 a

end Int

end CrossedProduct
end Pestov91
end GroupApproximation

#audit_axioms GroupApproximation.Pestov91.CrossedProduct.coeffMap_single
#audit_axioms GroupApproximation.Pestov91.CrossedProduct.coeff_coeffMap
#audit_axioms GroupApproximation.Pestov91.CrossedProduct.coeffMap_injective
#audit_axioms GroupApproximation.Pestov91.CrossedProduct.coeffMap_surjective
#audit_axioms GroupApproximation.Pestov91.CrossedProduct.coeffMap_C
