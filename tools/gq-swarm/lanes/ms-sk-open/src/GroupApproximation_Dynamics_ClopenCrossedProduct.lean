import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Pestov91.CrossedProduct
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.LocallyConstant.Algebra

/-!
# The clopen crossed product `R_X = LC(X, k) ⋊_T ℤ`

`non_mf_groups_exist.tex`, `\label{sec:chain-core}`, tex 1343–1352:

> Let $X$ be a nonempty compact metrizable zero-dimensional space, and let $T\colon X\to X$ be a
> homeomorphism.  For a finite field $k$, put
> $R_X=\operatorname{LC}(X,k)\rtimes_T\mathbb Z$, $ufu^{-1}=f\circ T^{-1}$.
> Here $\operatorname{LC}$ denotes locally constant functions and the crossed product is
> algebraic: its elements have unique finite Laurent expansions $\sum_j f_j u^j$.  The powers of
> $u$ remain formal even if $T$ has finite order.

This module is the interface of `R_X` for the `sec:chain-core` modules.  Its definitions hold for
every topological space `X`, homeomorphism `T` and ring `k`; the printed hypotheses on `X` and `k`
belong to the theorems that use them.

* `ClopenCoeff T k`: a type synonym for `LocallyConstant X k` carrying the action of `ℤ` through
  `T`, with `ClopenCoeff.of : LocallyConstant X k ≃+* ClopenCoeff T k`;
* `ClopenCoeff.smul_of`: `ofAdd j • of f = of (f ∘ T ^ (-j))`, and
  `ClopenCoeff.ofAdd_one_smul_of`: `ofAdd 1 • of f = of (f ∘ T⁻¹)`;
* `ClopenCrossedProduct T k`: the ring `R_X`, as
  `SkewMonoidAlgebra (ClopenCoeff T k) (Multiplicative ℤ)` (`Pestov91.CrossedProduct`).  Its
  elements are the finitely supported functions `ℤ → LC(X, k)`, so Laurent expansions are unique
  and the powers of `u` are formal;
* `ClopenCrossedProduct.coeff : LocallyConstant X k →+* R_X` and the implementing unit
  `ClopenCrossedProduct.unit`;
* `ClopenCrossedProduct.unit_mul_coeff_mul_inv`: `u * coeff f * u⁻¹ = coeff (f ∘ T⁻¹)`;
* `ClopenCrossedProduct.exists_sum_coeff_mul_unit_zpow`: every element is `∑ j ∈ S, f_j u^j`;
* identities for `LocallyConstant.charFn`: `isClopen_image`, `charFn_mul_charFn_of_subset`,
  `charFn_mul_charFn_of_superset`, `charFn_sub_charFn_of_subset`, `comap_symm_charFn`.
-/

namespace GroupApproximation

open Multiplicative (ofAdd toAdd)

variable {X : Type*} [TopologicalSpace X]

/-- The coefficient ring `LC(X, k)` of `R_X` (tex 1346), as a type synonym for
`LocallyConstant X k` that carries the action of `ℤ` through the homeomorphism `T`. -/
def ClopenCoeff (_T : X ≃ₜ X) (k : Type*) : Type _ :=
  LocallyConstant X k

namespace ClopenCoeff

variable (T : X ≃ₜ X) (k : Type*) [Ring k]

instance instRing : Ring (ClopenCoeff T k) :=
  inferInstanceAs (Ring (LocallyConstant X k))

/-- The identity map `LC(X, k) ≃+* ClopenCoeff T k`. -/
def of : LocallyConstant X k ≃+* ClopenCoeff T k where
  toFun f := f
  invFun f := f
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- `ℤ` acts on `ClopenCoeff T k` through `T`: `ofAdd j` sends `f` to `f ∘ T ^ (-j)`. -/
noncomputable instance instMulSemiringAction :
    MulSemiringAction (Multiplicative ℤ) (ClopenCoeff T k) where
  smul j f := of T k
    (LocallyConstant.comap ⟨⇑(T ^ (-toAdd j)), (T ^ (-toAdd j)).continuous⟩ ((of T k).symm f))
  one_smul f := LocallyConstant.ext fun x => by
    show (of T k).symm f ((T ^ (-toAdd (1 : Multiplicative ℤ))) x) = (of T k).symm f x
    rw [toAdd_one, neg_zero, zpow_zero, Homeomorph.one_apply]
  mul_smul m n f := LocallyConstant.ext fun x => by
    show (of T k).symm f ((T ^ (-toAdd (m * n))) x) =
      (of T k).symm f ((T ^ (-toAdd n)) ((T ^ (-toAdd m)) x))
    rw [toAdd_mul, neg_add_rev, zpow_add, Homeomorph.mul_apply]
  smul_zero _ := LocallyConstant.ext fun _ => rfl
  smul_add _ _ _ := LocallyConstant.ext fun _ => rfl
  smul_one _ := LocallyConstant.ext fun _ => rfl
  smul_mul _ _ _ := LocallyConstant.ext fun _ => rfl

theorem smul_of (j : ℤ) (f : LocallyConstant X k) :
    ofAdd j • of T k f =
      of T k (LocallyConstant.comap ⟨⇑(T ^ (-j)), (T ^ (-j)).continuous⟩ f) :=
  rfl

/-- The action of `ofAdd 1` is `f ↦ f ∘ T⁻¹`. -/
theorem ofAdd_one_smul_of (f : LocallyConstant X k) :
    ofAdd (1 : ℤ) • of T k f =
      of T k (LocallyConstant.comap ⟨⇑T.symm, T.symm.continuous⟩ f) :=
  LocallyConstant.ext fun x => by
    show f ((T ^ (-(1 : ℤ))) x) = f (T.symm x)
    rw [zpow_neg_one, Homeomorph.inv_apply]

end ClopenCoeff

/-- **The ring** `R_X = LC(X, k) ⋊_T ℤ` (tex 1346–1347): the algebraic crossed product
`SkewMonoidAlgebra (ClopenCoeff T k) (Multiplicative ℤ)`. -/
abbrev ClopenCrossedProduct (T : X ≃ₜ X) (k : Type*) [Ring k] : Type _ :=
  SkewMonoidAlgebra (ClopenCoeff T k) (Multiplicative ℤ)

namespace ClopenCrossedProduct

section Ring

variable (T : X ≃ₜ X) (k : Type*) [Ring k]

/-- The coefficient embedding `LC(X, k) →+* R_X`. -/
noncomputable def coeff : LocallyConstant X k →+* ClopenCrossedProduct T k :=
  RingHom.comp Pestov91.CrossedProduct.C (ClopenCoeff.of T k).toRingHom

theorem coeff_apply (f : LocallyConstant X k) :
    coeff T k f = Pestov91.CrossedProduct.C (ClopenCoeff.of T k f) :=
  rfl

/-- The implementing unit `u` of `R_X`. -/
noncomputable abbrev unit : (ClopenCrossedProduct T k)ˣ :=
  Pestov91.CrossedProduct.unit

/-- `u * f = (f ∘ T⁻¹) * u`. -/
theorem unit_mul_coeff (f : LocallyConstant X k) :
    (unit T k : ClopenCrossedProduct T k) * coeff T k f =
      coeff T k (LocallyConstant.comap ⟨⇑T.symm, T.symm.continuous⟩ f) *
        (unit T k : ClopenCrossedProduct T k) := by
  have h := Pestov91.CrossedProduct.unit_zpow_mul_C (A := ClopenCoeff T k) 1
    (ClopenCoeff.of T k f)
  rw [zpow_one, ClopenCoeff.ofAdd_one_smul_of] at h
  exact h

/-- **Covariance** (tex 1347): `u f u⁻¹ = f ∘ T⁻¹`. -/
theorem unit_mul_coeff_mul_inv (f : LocallyConstant X k) :
    (unit T k : ClopenCrossedProduct T k) * coeff T k f * ↑(unit T k)⁻¹ =
      coeff T k (LocallyConstant.comap ⟨⇑T.symm, T.symm.continuous⟩ f) := by
  rw [unit_mul_coeff, mul_assoc, Units.mul_inv, mul_one]

/-- **Laurent form** (tex 1349–1350): every element of `R_X` is a finite sum `∑ j ∈ S, f_j u^j`. -/
theorem exists_sum_coeff_mul_unit_zpow (x : ClopenCrossedProduct T k) :
    ∃ (S : Finset ℤ) (f : ℤ → LocallyConstant X k),
      x = ∑ j ∈ S, coeff T k (f j) *
        ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) :=
  Pestov91.CrossedProduct.exists_sum_C_mul_unit_zpow x

end Ring

section Indicator

/-- `T(P)` is clopen when `P` is. -/
theorem isClopen_image (T : X ≃ₜ X) {P : Set X} (hP : IsClopen P) : IsClopen (T '' P) := by
  rw [T.image_eq_preimage_symm]
  exact hP.preimage T.symm.continuous

variable (k : Type*) [Ring k]

theorem charFn_mul_charFn_of_subset {U V : Set X} (hU : IsClopen U) (hV : IsClopen V)
    (h : U ⊆ V) :
    LocallyConstant.charFn k hU * LocallyConstant.charFn k hV = LocallyConstant.charFn k hU := by
  ext x
  simp only [LocallyConstant.mul_apply, LocallyConstant.coe_charFn]
  by_cases hx : x ∈ U
  · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (h hx), Pi.one_apply, mul_one]
  · simp only [Set.indicator_of_notMem hx, zero_mul]

theorem charFn_mul_charFn_of_superset {U V : Set X} (hU : IsClopen U) (hV : IsClopen V)
    (h : V ⊆ U) :
    LocallyConstant.charFn k hU * LocallyConstant.charFn k hV = LocallyConstant.charFn k hV := by
  ext x
  simp only [LocallyConstant.mul_apply, LocallyConstant.coe_charFn]
  by_cases hx : x ∈ V
  · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (h hx), Pi.one_apply, mul_one]
  · simp only [Set.indicator_of_notMem hx, mul_zero]

theorem charFn_sub_charFn_of_subset {U V : Set X} (hU : IsClopen U) (hV : IsClopen V)
    (h : V ⊆ U) :
    LocallyConstant.charFn k hU - LocallyConstant.charFn k hV =
      LocallyConstant.charFn k (hU.diff hV) := by
  ext x
  simp only [LocallyConstant.sub_apply, LocallyConstant.coe_charFn]
  by_cases hxV : x ∈ V
  · have hd : x ∉ U \ V := fun hx => hx.2 hxV
    simp only [Set.indicator_of_mem (h hxV), Set.indicator_of_mem hxV,
      Set.indicator_of_notMem hd, sub_self]
  · by_cases hxU : x ∈ U
    · have hd : x ∈ U \ V := ⟨hxU, hxV⟩
      simp only [Set.indicator_of_mem hxU, Set.indicator_of_notMem hxV,
        Set.indicator_of_mem hd, sub_zero]
    · have hd : x ∉ U \ V := fun hx => hxU hx.1
      simp only [Set.indicator_of_notMem hxU, Set.indicator_of_notMem hxV,
        Set.indicator_of_notMem hd, sub_zero]

/-- `1_P ∘ T⁻¹ = 1_{T(P)}`. -/
theorem comap_symm_charFn (T : X ≃ₜ X) {P : Set X} (hP : IsClopen P) :
    LocallyConstant.comap ⟨⇑T.symm, T.symm.continuous⟩ (LocallyConstant.charFn k hP) =
      LocallyConstant.charFn k (isClopen_image T hP) := by
  have hmem : ∀ x, x ∈ T '' P ↔ T.symm x ∈ P := fun x => by
    rw [T.image_eq_preimage_symm, Set.mem_preimage]
  ext x
  rw [LocallyConstant.coe_comap_apply]
  simp only [LocallyConstant.coe_charFn, ContinuousMap.coe_mk]
  by_cases hx : T.symm x ∈ P
  · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem ((hmem x).2 hx), Pi.one_apply]
  · simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hmem x).1 hx)]

end Indicator

end ClopenCrossedProduct

end GroupApproximation

open GroupApproximation

#audit_axioms GroupApproximation.ClopenCrossedProduct.unit_mul_coeff_mul_inv
#audit_axioms GroupApproximation.ClopenCrossedProduct.comap_symm_charFn
