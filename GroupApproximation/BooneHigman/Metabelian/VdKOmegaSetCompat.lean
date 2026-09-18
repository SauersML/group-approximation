import GroupApproximation.BooneHigman.Metabelian.VdKOmegaGen
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Building `Ω` on `P̃ × X`, part 1: the lift condition, checked on generators

Lane `bh-met-93a`.  Generic group theory, unconditional.

A homomorphism out of a semidirect product `N ⋊[φ] S` is `SemidirectProduct.lift f₁ f₂ h`,
and the side condition `h` asks, for every `g : S` and every `w : N`,

  `vdkOmegaSet_CompatAt φ f₁ f₂ g : f₁ (φ g w) = f₂ g * f₁ w * (f₂ g)⁻¹`.

* `vdkOmegaSet_compatSubgroup`: the `g` satisfying it form a subgroup of `S`.  So when `S` is a
  presented group it is enough to check the condition on generators.
* `vdkOmegaSet_compatAt_of_single`: when `N = R^n` (written multiplicatively), it is enough to
  check the condition on the unit vectors `b e_k` (`vdkOmegaSet_hom_ext_single`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

section Compat

variable {S N H : Type*} [Group S] [Group N] [Group H]

/-- The lift condition of `SemidirectProduct.lift` at one element `g : S`. -/
def vdkOmegaSet_CompatAt (φ : S →* MulAut N) (f₁ : N →* H) (f₂ : S →* H) (g : S) : Prop :=
  ∀ w : N, f₁ (φ g w) = f₂ g * f₁ w * (f₂ g)⁻¹

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_CompatAt

variable (φ : S →* MulAut N) (f₁ : N →* H) (f₂ : S →* H)

theorem vdkOmegaSet_compatAt_one : vdkOmegaSet_CompatAt φ f₁ f₂ 1 := by
  intro w
  simp only [map_one, MulAut.one_apply, one_mul, inv_one, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_compatAt_one

theorem vdkOmegaSet_compatAt_mul {g h : S} (hg : vdkOmegaSet_CompatAt φ f₁ f₂ g)
    (hh : vdkOmegaSet_CompatAt φ f₁ f₂ h) : vdkOmegaSet_CompatAt φ f₁ f₂ (g * h) := by
  intro w
  rw [map_mul φ, MulAut.mul_apply, hg, hh, map_mul f₂]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_compatAt_mul

theorem vdkOmegaSet_compatAt_inv {g : S} (hg : vdkOmegaSet_CompatAt φ f₁ f₂ g) :
    vdkOmegaSet_CompatAt φ f₁ f₂ g⁻¹ := by
  intro w
  have e := hg (φ g⁻¹ w)
  rw [map_inv φ g, MulAut.apply_inv_self] at e
  rw [map_inv f₂ g, map_inv φ g, e]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_compatAt_inv

/-- The elements `g : S` at which the lift condition holds form a subgroup. -/
def vdkOmegaSet_compatSubgroup : Subgroup S where
  carrier := {g | vdkOmegaSet_CompatAt φ f₁ f₂ g}
  mul_mem' {a b} ha hb := vdkOmegaSet_compatAt_mul φ f₁ f₂ (g := a) (h := b) ha hb
  one_mem' := vdkOmegaSet_compatAt_one φ f₁ f₂
  inv_mem' {a} ha := vdkOmegaSet_compatAt_inv φ f₁ f₂ (g := a) ha

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_compatSubgroup

/-- The lift condition at every `g`, in the exact form `SemidirectProduct.lift` takes. -/
theorem vdkOmegaSet_lift_of_compatAt (h : ∀ g, vdkOmegaSet_CompatAt φ f₁ f₂ g) (g : S) :
    f₁.comp (φ g).toMonoidHom = (MulAut.conj (f₂ g)).toMonoidHom.comp f₁ := by
  refine MonoidHom.ext fun w ↦ ?_
  change f₁ (φ g w) = f₂ g * f₁ w * (f₂ g)⁻¹
  exact h g w

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_lift_of_compatAt

end Compat

section Single

variable {n : ℕ} {R : Type*} [CommRing R] {H : Type*} [Group H]

/-- Two homomorphisms out of `R^n` (written multiplicatively) that agree on every unit vector
`b e_k` are equal. -/
theorem vdkOmegaSet_hom_ext_single {f₁ f₂ : Multiplicative (Fin n → R) →* H}
    (h : ∀ (k : Fin n) (b : R), f₁ (Multiplicative.ofAdd (Pi.single k b)) =
      f₂ (Multiplicative.ofAdd (Pi.single k b)))
    (w : Multiplicative (Fin n → R)) : f₁ w = f₂ w := by
  have key : ∀ v : Fin n → R,
      f₁ (Multiplicative.ofAdd v) = f₂ (Multiplicative.ofAdd v) := by
    intro v
    induction v using Pi.single_induction with
    | zero => simp only [ofAdd_zero, map_one]
    | add u₁ u₂ h₁ h₂ => rw [ofAdd_add, map_mul, map_mul, h₁, h₂]
    | single k b => exact h k b
  have e := key (Multiplicative.toAdd w)
  rwa [ofAdd_toAdd] at e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_hom_ext_single

/-- For `N = R^n`, the lift condition at `g` follows from the unit vectors `b e_k`. -/
theorem vdkOmegaSet_compatAt_of_single {S : Type*} [Group S]
    (φ : S →* MulAut (Multiplicative (Fin n → R))) (f₁ : Multiplicative (Fin n → R) →* H)
    (f₂ : S →* H) (g : S)
    (h : ∀ (k : Fin n) (b : R), f₁ (φ g (Multiplicative.ofAdd (Pi.single k b))) =
      f₂ g * f₁ (Multiplicative.ofAdd (Pi.single k b)) * (f₂ g)⁻¹) :
    vdkOmegaSet_CompatAt φ f₁ f₂ g := by
  intro w
  exact vdkOmegaSet_hom_ext_single (f₁ := f₁.comp (φ g).toMonoidHom)
    (f₂ := (MulAut.conj (f₂ g)).toMonoidHom.comp f₁) h w

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_compatAt_of_single

end Single

end GroupApproximation.BooneHigman.Metabelian.ElemFP
