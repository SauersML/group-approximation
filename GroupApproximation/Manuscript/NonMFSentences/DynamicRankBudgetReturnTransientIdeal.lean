import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudgetReturnBridge
import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudgetInducedCore
import GroupApproximation.Dynamics.ReturnRingInjective
import GroupApproximation.Algebra.ZCrossedProductLift
import GroupApproximation.Dynamics.TransientIdealExact
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:dynamic-rank-budget`: `θ⁻¹(p_C I p_C)` lies in the return transient ideal

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1750:

> The return transient ideal is therefore $J=p_CIp_C$.

This module proves the inclusion used later, `returnTransientIdealStatement_holds :
ReturnTransientIdealStatement`, for every ring isomorphism `θ : R_C ≅ p_C R_X p_C` with the two
properties of `ReturnRingCrossedProductStatement`.

* `theta_eq_returnRingHom`: such a `θ` agrees with the landed `returnRingHom`
  (`Dynamics/ReturnRingLift`), since both send coefficients to their extensions by zero and the unit
  to `v` (`Pestov91.CrossedProduct.ringHom_ext`).
* `coeff_one_theta`: on `C`, the zeroth Laurent coefficient of `θ c` is that of `c`, from the landed
  readout `coeff_one_coe_returnRingHom`.
* Right multiplication by `u_S^{-j}` moves the coefficient at `j` to exponent `0`
  (`coeff_mul_unit_zpow_neg_toAdd`), and the transient ideal is a right ideal, so every coefficient
  of `c` vanishes on `C ∩ Y` when `θ c ∈ I`.
* `CR(S_C) ⊆ C ∩ Y` (`coe_mem_chainRecurrentSet_of_firstReturn`) gives membership in the return
  transient ideal.
-/

namespace GroupApproximation.ChainCore.DynamicRankBudget

open MFQuotientUnits SkewMonoidAlgebra
open Multiplicative (ofAdd toAdd)

/-- Right multiplication by `u^{-j}` moves the Laurent coefficient at `j` to exponent `0`. -/
theorem coeff_mul_unit_zpow_neg_toAdd {B : Type*} [Ring B] [MulSemiringAction (Multiplicative ℤ) B]
    (c : SkewMonoidAlgebra B (Multiplicative ℤ)) (g : Multiplicative ℤ) :
    (c * ((Pestov91.CrossedProduct.unit ^ (-toAdd g) : (SkewMonoidAlgebra B (Multiplicative ℤ))ˣ) :
      SkewMonoidAlgebra B (Multiplicative ℤ))).coeff 1 = c.coeff g := by
  rw [Pestov91.CrossedProduct.val_unit_zpow, coeff_mul_single, one_mul, smul_one, mul_one, ofAdd_neg,
    inv_inv, ofAdd_toAdd]

/-- The same shift in `R_X`, spelled with `ClopenCrossedProduct.unit`. -/
theorem clopen_coeff_mul_unit_zpow_neg_toAdd {Y : Type*} [TopologicalSpace Y] (S : Y ≃ₜ Y)
    (k : Type*) [Ring k] (c : ClopenCrossedProduct S k) (g : Multiplicative ℤ) :
    SkewMonoidAlgebra.coeff (c * ((ClopenCrossedProduct.unit S k ^ (-toAdd g) :
      (ClopenCrossedProduct S k)ˣ) : ClopenCrossedProduct S k)) 1 = SkewMonoidAlgebra.coeff c g :=
  coeff_mul_unit_zpow_neg_toAdd (B := ClopenCoeff S k) c g

section Return

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {r : ℕ} {C : Set X} (k : Type*) [Ring k]
  (hC : IsReturnSection T r C)
  {hp : IsIdempotentElem
    (ClopenCrossedProduct.coeff T k (LocallyConstant.charFn k hC.isClopen))}
  (θ : ClopenCrossedProduct (firstReturnHomeomorph hC) k ≃+*
    Corner (ClopenCrossedProduct T k)
      (ClopenCrossedProduct.coeff T k (LocallyConstant.charFn k hC.isClopen)) hp)

/-- The printed unit clause of `ReturnRingCrossedProductStatement` says that `θ u_S = v`. -/
theorem coe_theta_unit
    (hunit : ∃ v : ℕ → LocallyConstant X k,
        (∀ (h : ℕ) (x : X), v h x = Set.indicator {y | y ∈ C ∧ returnTime T C y = h} 1 x) ∧
        ((θ ((ClopenCrossedProduct.unit (firstReturnHomeomorph hC) k :
            (ClopenCrossedProduct (firstReturnHomeomorph hC) k)ˣ) :
              ClopenCrossedProduct (firstReturnHomeomorph hC) k) : ClopenCrossedProduct T k)) =
          ∑ h ∈ Finset.range (2 * r),
            ((ClopenCrossedProduct.unit T k ^ (h : ℤ) : (ClopenCrossedProduct T k)ˣ) :
              ClopenCrossedProduct T k) * ClopenCrossedProduct.coeff T k (v h)) :
    ((θ ((ClopenCrossedProduct.unit (firstReturnHomeomorph hC) k :
        (ClopenCrossedProduct (firstReturnHomeomorph hC) k)ˣ) :
          ClopenCrossedProduct (firstReturnHomeomorph hC) k) : ClopenCrossedProduct T k)) =
      returnV k hC := by
  obtain ⟨v, hv, hθ⟩ := hunit
  rw [hθ, returnV]
  refine Finset.sum_congr rfl fun h _ => congrArg₂ (· * ·) rfl ?_
  rw [cellCoeff]
  congr 1
  ext x
  rw [hv, LocallyConstant.coe_charFn]
  rfl

/-- The printed coefficient clause of `ReturnRingCrossedProductStatement`, at a Laurent monomial. -/
theorem coe_theta_C
    (hcoef : ∀ (f : LocallyConstant C k) (g : LocallyConstant X k),
        (∀ x : C, g x = f x) → (∀ x : X, x ∉ C → g x = 0) →
          ((θ (ClopenCrossedProduct.coeff (firstReturnHomeomorph hC) k f) :
            ClopenCrossedProduct T k)) = ClopenCrossedProduct.coeff T k g)
    (a : ClopenCoeff (firstReturnHomeomorph hC) k) :
    ((θ (Pestov91.CrossedProduct.C a) : ClopenCrossedProduct T k)) =
      ClopenCrossedProduct.coeff T k (clopenExtendByZero k hC.isClopen
        ((ClopenCoeff.of (firstReturnHomeomorph hC) k).symm a)) := by
  have hCa : (Pestov91.CrossedProduct.C a : ClopenCrossedProduct (firstReturnHomeomorph hC) k) =
      ClopenCrossedProduct.coeff (firstReturnHomeomorph hC) k
        ((ClopenCoeff.of (firstReturnHomeomorph hC) k).symm a) := by
    rw [ClopenCrossedProduct.coeff_apply, RingEquiv.apply_symm_apply]
  rw [hCa]
  exact hcoef _ _ (fun x => clopenExtendByZero_apply_of_mem k hC.isClopen _ x.2)
    (fun x hx => clopenExtendByZero_apply_of_notMem k hC.isClopen _ hx)

/-- **A return ring iso with the printed properties is `returnRingHom`.** -/
theorem theta_eq_returnRingHom
    (hcoef : ∀ (f : LocallyConstant C k) (g : LocallyConstant X k),
        (∀ x : C, g x = f x) → (∀ x : X, x ∉ C → g x = 0) →
          ((θ (ClopenCrossedProduct.coeff (firstReturnHomeomorph hC) k f) :
            ClopenCrossedProduct T k)) = ClopenCrossedProduct.coeff T k g)
    (hunit : ∃ v : ℕ → LocallyConstant X k,
        (∀ (h : ℕ) (x : X), v h x = Set.indicator {y | y ∈ C ∧ returnTime T C y = h} 1 x) ∧
        ((θ ((ClopenCrossedProduct.unit (firstReturnHomeomorph hC) k :
            (ClopenCrossedProduct (firstReturnHomeomorph hC) k)ˣ) :
              ClopenCrossedProduct (firstReturnHomeomorph hC) k) : ClopenCrossedProduct T k)) =
          ∑ h ∈ Finset.range (2 * r),
            ((ClopenCrossedProduct.unit T k ^ (h : ℤ) : (ClopenCrossedProduct T k)ˣ) :
              ClopenCrossedProduct T k) * ClopenCrossedProduct.coeff T k (v h)) :
    (θ : ClopenCrossedProduct (firstReturnHomeomorph hC) k →+*
      Corner (ClopenCrossedProduct T k)
        (ClopenCrossedProduct.coeff T k (LocallyConstant.charFn k hC.isClopen)) hp) =
      returnRingHom k hC := by
  refine Pestov91.CrossedProduct.ringHom_ext (fun a => corner_ext ?_) (corner_ext ?_)
  · show ((θ (Pestov91.CrossedProduct.C a) : Corner (ClopenCrossedProduct T k)
        (ClopenCrossedProduct.coeff T k (LocallyConstant.charFn k hC.isClopen)) hp) :
          ClopenCrossedProduct T k) =
      ((returnRingHom k hC (Pestov91.CrossedProduct.C a) : ReturnCorner k hC) :
        ClopenCrossedProduct T k)
    have hCa : (Pestov91.CrossedProduct.C a : ClopenCrossedProduct (firstReturnHomeomorph hC) k) =
        ClopenCrossedProduct.coeff (firstReturnHomeomorph hC) k
          ((ClopenCoeff.of (firstReturnHomeomorph hC) k).symm a) := by
      rw [ClopenCrossedProduct.coeff_apply, RingEquiv.apply_symm_apply]
    rw [coe_theta_C k hC θ hcoef, hCa, coe_returnRingHom_coeff]
  · exact (coe_theta_unit k hC θ hunit).trans (coe_returnRingHom_unit k hC).symm

/-- **The zeroth Laurent coefficient is compatible with the return ring iso on `C`.** -/
theorem coeff_one_theta
    (hcoef : ∀ (f : LocallyConstant C k) (g : LocallyConstant X k),
        (∀ x : C, g x = f x) → (∀ x : X, x ∉ C → g x = 0) →
          ((θ (ClopenCrossedProduct.coeff (firstReturnHomeomorph hC) k f) :
            ClopenCrossedProduct T k)) = ClopenCrossedProduct.coeff T k g)
    (hunit : ∃ v : ℕ → LocallyConstant X k,
        (∀ (h : ℕ) (x : X), v h x = Set.indicator {y | y ∈ C ∧ returnTime T C y = h} 1 x) ∧
        ((θ ((ClopenCrossedProduct.unit (firstReturnHomeomorph hC) k :
            (ClopenCrossedProduct (firstReturnHomeomorph hC) k)ˣ) :
              ClopenCrossedProduct (firstReturnHomeomorph hC) k) : ClopenCrossedProduct T k)) =
          ∑ h ∈ Finset.range (2 * r),
            ((ClopenCrossedProduct.unit T k ^ (h : ℤ) : (ClopenCrossedProduct T k)ˣ) :
              ClopenCrossedProduct T k) * ClopenCrossedProduct.coeff T k (v h))
    (c : ClopenCrossedProduct (firstReturnHomeomorph hC) k) (y : C) :
    (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff ((θ c : ClopenCrossedProduct T k)) 1) (y : X) =
      (ClopenCoeff.of (firstReturnHomeomorph hC) k).symm (SkewMonoidAlgebra.coeff c 1) y := by
  have h' : ((θ c : Corner (ClopenCrossedProduct T k)
        (ClopenCrossedProduct.coeff T k (LocallyConstant.charFn k hC.isClopen)) hp) :
          ClopenCrossedProduct T k) =
      ((returnRingHom k hC c : ReturnCorner k hC) : ClopenCrossedProduct T k) :=
    congrArg Subtype.val (RingHom.congr_fun (theta_eq_returnRingHom k hC θ hcoef hunit) c)
  rw [h', coeff_one_coe_returnRingHom, RingEquiv.symm_apply_apply]
  exact clopenExtendByZero_apply_of_mem k hC.isClopen _ y.2

end Return

/-- **`θ⁻¹(p_C I p_C)` lies in the return transient ideal** (tex 1750, "The return transient ideal is
therefore $J=p_CIp_C$", the inclusion used at tex 1752–1757), closed. -/
theorem returnTransientIdealStatement_holds : ReturnTransientIdealStatement := by
  intro X _ _ _ T r C hC hr _ k _ _ hp θ hcoef hunit c hc
  refine (ClopenCrossedProduct.mem_transientIdeal_iff_forall_coeff _ _ _).2 fun g y hy => ?_
  have hyT : (y : X) ∈ Dynamics.chainRecurrentSet ⇑T :=
    coe_mem_chainRecurrentSet_of_firstReturn hC hy
  have hmem : ((θ (c * ((ClopenCrossedProduct.unit (firstReturnHomeomorph hC) k ^ (-toAdd g) :
        (ClopenCrossedProduct (firstReturnHomeomorph hC) k)ˣ) :
          ClopenCrossedProduct (firstReturnHomeomorph hC) k)) : ClopenCrossedProduct T k)) ∈
      ClopenCrossedProduct.coreTransientIdeal T k := by
    rw [map_mul, coe_corner_mul]
    exact (ClopenCrossedProduct.coreTransientIdeal T k).mul_mem_right _ _ hc
  have h0 := (ClopenCrossedProduct.mem_transientIdeal_iff_forall_coeff _ _ _).1 hmem 1 (y : X) hyT
  rw [coeff_one_theta k hC θ hcoef hunit, clopen_coeff_mul_unit_zpow_neg_toAdd] at h0
  exact h0

end GroupApproximation.ChainCore.DynamicRankBudget

/-! ### Audit -/

#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.coeff_mul_unit_zpow_neg_toAdd
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.clopen_coeff_mul_unit_zpow_neg_toAdd
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.coe_theta_C
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.coe_theta_unit
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.theta_eq_returnRingHom
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.coeff_one_theta
#audit_closed_axioms GroupApproximation.ChainCore.DynamicRankBudget.returnTransientIdealStatement_holds
