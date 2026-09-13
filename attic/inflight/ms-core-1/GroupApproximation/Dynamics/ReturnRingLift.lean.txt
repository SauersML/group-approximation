import GroupApproximation.Dynamics.ReturnRingUnit
import GroupApproximation.Algebra.ZCrossedProductLift

/-!
# The map `LC(C, k) ⋊_{S_C} ℤ → P_C`

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1721–1726:

> Let $C_h$ be the clopen first-return-time cells and $S_C$ the
> first-return homeomorphism.  Put $p_C=1_C$ and $P_C=p_CR_Xp_C$.
> The unit $v=\sum_h u^h1_{C_h}$ implements $S_C$, and
> $P_C=\operatorname{LC}(C,k)\rtimes_{S_C}\mathbb Z$: split any
> partial shift with endpoints in $C$ according to its successive
> returns.

For a return section `C` of `T` (`IsReturnSection T r C`), with `S_C = firstReturnHomeomorph hC`:

* `extendCorner k hC f`: the extension of `f ∈ LC(C, k)` by zero, as an element of
  `P_C = ReturnCorner k hC`;
* `returnCoeffHom k hC : LC(C, k) →+* P_C`, a unital ring homomorphism (the unit of `P_C` is
  `p_C = 1_C`);
* `returnUnit_mul_returnCoeffHom`: `v` implements `S_C` on these coefficients, in `P_C`;
* `returnRingHom k hC : LC(C, k) ⋊_{S_C} ℤ →+* P_C`, the lift along the covariant pair
  (`Pestov91.CrossedProduct.liftOfUnit`), with `coe_returnRingHom_coeff` (coefficients go to their
  extensions by zero), `coe_returnRingHom_unit` (`u ↦ v`), `coe_returnRingHom_unit_inv`
  (`u⁻¹ ↦ w`) and `coe_returnRingHom_unit_zpow`.

The unit `returnUnit`, its inverse `w`, and the covariance `returnV_mul_coeff_extend` are
ct-return-tower's (`Dynamics/ReturnRingUnit`).
-/

namespace GroupApproximation.ChainCore

open Set MFQuotientUnits
open Multiplicative (ofAdd toAdd)

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {r : ℕ} {C : Set X}

section Lift

variable (k : Type*) [Ring k] (hC : IsReturnSection T r C)

/-- `f ∈ LC(C, k)` extended by zero, as an element of `P_C`. -/
noncomputable def extendCorner (f : LocallyConstant C k) : ReturnCorner k hC :=
  ⟨ClopenCrossedProduct.coeff T k (clopenExtendByZero k hC.isClopen f),
    by rw [returnP, ← map_mul, clopenExtendByZero_charFn_mul],
    by rw [returnP, ← map_mul, clopenExtendByZero_mul_charFn]⟩

theorem coe_extendCorner (f : LocallyConstant C k) :
    ((extendCorner k hC f : ReturnCorner k hC) : ClopenCrossedProduct T k) =
      ClopenCrossedProduct.coeff T k (clopenExtendByZero k hC.isClopen f) :=
  rfl

/-- **The coefficient map** `LC(C, k) →+* P_C`: extension by zero. -/
noncomputable def returnCoeffHom :
    ClopenCoeff (firstReturnHomeomorph hC) k →+* ReturnCorner k hC where
  toFun a := extendCorner k hC ((ClopenCoeff.of (firstReturnHomeomorph hC) k).symm a)
  map_one' := corner_ext (by
    show ClopenCrossedProduct.coeff T k (clopenExtendByZero k hC.isClopen
      ((ClopenCoeff.of (firstReturnHomeomorph hC) k).symm 1)) = returnP k hC
    rw [map_one, clopenExtendByZero_one, returnP])
  map_mul' a b := corner_ext (by
    show ClopenCrossedProduct.coeff T k (clopenExtendByZero k hC.isClopen
        ((ClopenCoeff.of (firstReturnHomeomorph hC) k).symm (a * b))) =
      ClopenCrossedProduct.coeff T k (clopenExtendByZero k hC.isClopen
          ((ClopenCoeff.of (firstReturnHomeomorph hC) k).symm a)) *
        ClopenCrossedProduct.coeff T k (clopenExtendByZero k hC.isClopen
          ((ClopenCoeff.of (firstReturnHomeomorph hC) k).symm b))
    rw [map_mul, clopenExtendByZero_mul, map_mul])
  map_zero' := corner_ext (by
    show ClopenCrossedProduct.coeff T k (clopenExtendByZero k hC.isClopen
      ((ClopenCoeff.of (firstReturnHomeomorph hC) k).symm 0)) = 0
    rw [map_zero, clopenExtendByZero_zero, map_zero])
  map_add' a b := corner_ext (by
    show ClopenCrossedProduct.coeff T k (clopenExtendByZero k hC.isClopen
        ((ClopenCoeff.of (firstReturnHomeomorph hC) k).symm (a + b))) =
      ClopenCrossedProduct.coeff T k (clopenExtendByZero k hC.isClopen
          ((ClopenCoeff.of (firstReturnHomeomorph hC) k).symm a)) +
        ClopenCrossedProduct.coeff T k (clopenExtendByZero k hC.isClopen
          ((ClopenCoeff.of (firstReturnHomeomorph hC) k).symm b))
    rw [map_add, clopenExtendByZero_add, map_add])

theorem coe_returnCoeffHom (a : ClopenCoeff (firstReturnHomeomorph hC) k) :
    ((returnCoeffHom k hC a : ReturnCorner k hC) : ClopenCrossedProduct T k) =
      ClopenCrossedProduct.coeff T k (clopenExtendByZero k hC.isClopen
        ((ClopenCoeff.of (firstReturnHomeomorph hC) k).symm a)) :=
  rfl

/-- **`v` implements `S_C` in `P_C`**: `v · f = (f ∘ S_C⁻¹) · v` for coefficients extended by
zero. -/
theorem returnUnit_mul_returnCoeffHom (a : ClopenCoeff (firstReturnHomeomorph hC) k) :
    ((returnUnit k hC : (ReturnCorner k hC)ˣ) : ReturnCorner k hC) * returnCoeffHom k hC a =
      returnCoeffHom k hC (ofAdd (1 : ℤ) • a) *
        ((returnUnit k hC : (ReturnCorner k hC)ˣ) : ReturnCorner k hC) := by
  obtain ⟨f, rfl⟩ := (ClopenCoeff.of (firstReturnHomeomorph hC) k).surjective a
  refine corner_ext ?_
  rw [coe_corner_mul, coe_corner_mul, coe_returnUnit, coe_returnCoeffHom, coe_returnCoeffHom,
    ClopenCoeff.ofAdd_one_smul_of, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply,
    returnV_mul_coeff_extend]

/-- **The return ring map** `LC(C, k) ⋊_{S_C} ℤ →+* P_C`: coefficients go to their extensions by
zero and the implementing unit goes to `v`. -/
noncomputable def returnRingHom :
    ClopenCrossedProduct (firstReturnHomeomorph hC) k →+* ReturnCorner k hC :=
  Pestov91.CrossedProduct.liftOfUnit (returnCoeffHom k hC) (returnUnit k hC)
    (returnUnit_mul_returnCoeffHom k hC)

/-- Coefficients go to their extensions by zero. -/
theorem coe_returnRingHom_coeff (f : LocallyConstant C k) :
    ((returnRingHom k hC (ClopenCrossedProduct.coeff (firstReturnHomeomorph hC) k f) :
      ReturnCorner k hC) : ClopenCrossedProduct T k) =
      ClopenCrossedProduct.coeff T k (clopenExtendByZero k hC.isClopen f) := by
  rw [returnRingHom, ClopenCrossedProduct.coeff_apply, Pestov91.CrossedProduct.liftOfUnit_C,
    coe_returnCoeffHom, RingEquiv.symm_apply_apply]

/-- `u ^ n ↦ v ^ n`. -/
theorem coe_returnRingHom_unit_zpow (n : ℤ) :
    ((returnRingHom k hC ((ClopenCrossedProduct.unit (firstReturnHomeomorph hC) k ^ n :
        (ClopenCrossedProduct (firstReturnHomeomorph hC) k)ˣ) :
          ClopenCrossedProduct (firstReturnHomeomorph hC) k) : ReturnCorner k hC) :
      ClopenCrossedProduct T k) =
      (((returnUnit k hC ^ n : (ReturnCorner k hC)ˣ) : ReturnCorner k hC) :
        ClopenCrossedProduct T k) := by
  rw [returnRingHom, Pestov91.CrossedProduct.liftOfUnit_unit_zpow]

/-- `u ↦ v`. -/
theorem coe_returnRingHom_unit :
    ((returnRingHom k hC (ClopenCrossedProduct.unit (firstReturnHomeomorph hC) k :
        ClopenCrossedProduct (firstReturnHomeomorph hC) k) : ReturnCorner k hC) :
      ClopenCrossedProduct T k) = returnV k hC := by
  rw [returnRingHom, Pestov91.CrossedProduct.liftOfUnit_unit, coe_returnUnit]

/-- `u⁻¹ ↦ w`. -/
theorem coe_returnRingHom_unit_inv :
    ((returnRingHom k hC (((ClopenCrossedProduct.unit (firstReturnHomeomorph hC) k)⁻¹ :
        (ClopenCrossedProduct (firstReturnHomeomorph hC) k)ˣ) :
          ClopenCrossedProduct (firstReturnHomeomorph hC) k) : ReturnCorner k hC) :
      ClopenCrossedProduct T k) = returnW k hC := by
  have h := coe_returnRingHom_unit_zpow k hC (-1)
  rw [zpow_neg_one, zpow_neg_one, coe_returnUnit_inv] at h
  exact h

end Lift

end GroupApproximation.ChainCore

open GroupApproximation.ChainCore

#audit_axioms returnRingHom
#audit_axioms coe_returnRingHom_coeff
#audit_axioms coe_returnRingHom_unit
