import GroupApproximation.Manuscript.SimpleKazhdanSofic.Setting
import GroupApproximation.Dynamics.ClopenCrossedProductComap
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Group.Hom.Basic

/-!
# Conjugate and flip conjugate systems give isomorphic groups (simple_kazhdan_sofic_group.tex, "Questions")

`simple_kazhdan_sofic_group.tex` at the tip, section "Questions":

> If $(X,T)$ is topologically conjugate to $(Y,S)$ or to $(Y,S^{-1})$, then $G_X\cong G_Y$.

For homeomorphisms `T : X ≃ₜ X`, `S : Y ≃ₜ Y` and any ring `k`:

* `ringHom_ext_coeff_unit`: a ring homomorphism out of `R_T = LC(X,k) ⋊_T ℤ` is determined by its
  values on the coefficients `C(f)` and the powers `u^j`;
* `conjRingEquiv`: a conjugacy `φ ∘ T = S ∘ φ` gives `R_T ≃+* R_S`, with `C(f) ↦ C(f ∘ φ⁻¹)` and `u ↦ u`.
  Both directions are chain-core's `comap`, along `φ⁻¹` and along `φ`;
* `flipRingEquiv`: if `S' = S⁻¹` pointwise, then `R_S ≃+* R_{S'}`, with `C(f) ↦ C(f)` and `u ↦ u⁻¹`,
  since `u⁻¹ f u = f ∘ T` in `R_S` matches the covariance of `R_{S'}`;
* `nonempty_ringEquiv_of_conj_or_flip`, `nonempty_elementaryGroup_equiv_of_conj_or_flip`: a conjugacy
  to `(Y,S)` or to `(Y,S⁻¹)` gives `R_T ≃+* R_S` and `EL_n(R_T) ≃* EL_n(R_S)` for every `n`
  (`elementaryCoefficientEquiv`);
* `PrintedConjugacyIsomorphism`: the printed sentence for subshifts, `G_X = EL₃(R)`.
-/

namespace GroupApproximation

namespace SimpleKazhdanSofic

open ClopenCrossedProduct
open Multiplicative (ofAdd toAdd)
open SymbolicDynamics.FullShift

section Ext

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {k : Type*} [Ring k]

/-- A ring homomorphism out of `R_T` is determined by its values on `C(f)` and on `u^j`. -/
theorem ringHom_ext_coeff_unit {B : Type*} [Ring B] {f g : ClopenCrossedProduct T k →+* B}
    (hc : ∀ a : LocallyConstant X k, f (coeff T k a) = g (coeff T k a))
    (hu : ∀ j : ℤ, f ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) =
      g ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k)) : f = g := by
  refine RingHom.ext fun x => ?_
  obtain ⟨S, c, rfl⟩ := exists_sum_coeff_mul_unit_zpow T k x
  simp only [map_sum, map_mul, hc, hu]

end Ext

section Conjugacy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y}
  (k : Type*) [Ring k]

/-- The inverse of a conjugacy is a conjugacy. -/
theorem symm_conj (φ : X ≃ₜ Y) (hφ : ∀ x, φ (T x) = S (φ x)) (y : Y) :
    φ.symm (S y) = T (φ.symm y) := by
  rw [φ.symm_apply_eq, hφ, φ.apply_symm_apply]

/-- **The crossed-product isomorphism of a conjugacy** `φ ∘ T = S ∘ φ`: `C(f) ↦ C(f ∘ φ⁻¹)`,
`u ↦ u`. -/
noncomputable def conjRingEquiv (φ : X ≃ₜ Y) (hφ : ∀ x, φ (T x) = S (φ x)) :
    ClopenCrossedProduct T k ≃+* ClopenCrossedProduct S k :=
  RingEquiv.ofRingHom (comap k ⟨⇑φ.symm, φ.symm.continuous⟩ fun y => symm_conj φ hφ y)
    (comap k ⟨⇑φ, φ.continuous⟩ fun x => hφ x)
    (ringHom_ext_coeff_unit
      (fun a => by
        rw [RingHom.comp_apply, comap_coeff, comap_coeff, RingHom.id_apply]
        congr 1
        ext y
        show a (φ (φ.symm y)) = a y
        rw [φ.apply_symm_apply])
      fun j => by rw [RingHom.comp_apply, comap_unit_zpow, comap_unit_zpow, RingHom.id_apply])
    (ringHom_ext_coeff_unit
      (fun a => by
        rw [RingHom.comp_apply, comap_coeff, comap_coeff, RingHom.id_apply]
        congr 1
        ext x
        show a (φ.symm (φ x)) = a x
        rw [φ.symm_apply_apply])
      fun j => by rw [RingHom.comp_apply, comap_unit_zpow, comap_unit_zpow, RingHom.id_apply])

theorem conjRingEquiv_coeff (φ : X ≃ₜ Y) (hφ : ∀ x, φ (T x) = S (φ x)) (f : LocallyConstant X k) :
    conjRingEquiv k φ hφ (coeff T k f) =
      coeff S k (LocallyConstant.comap ⟨⇑φ.symm, φ.symm.continuous⟩ f) :=
  comap_coeff k ⟨⇑φ.symm, φ.symm.continuous⟩ (fun y => symm_conj φ hφ y) f

theorem conjRingEquiv_unit_zpow (φ : X ≃ₜ Y) (hφ : ∀ x, φ (T x) = S (φ x)) (j : ℤ) :
    conjRingEquiv k φ hφ ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) =
      ((unit S k ^ j : (ClopenCrossedProduct S k)ˣ) : ClopenCrossedProduct S k) :=
  comap_unit_zpow k ⟨⇑φ.symm, φ.symm.continuous⟩ (fun y => symm_conj φ hφ y) j

end Conjugacy

section Flip

variable {Y : Type*} [TopologicalSpace Y] (k : Type*) [Ring k]

theorem eq_inv_of_forall_apply_eq_symm {S S' : Y ≃ₜ Y} (h : ∀ y, S' y = S.symm y) : S' = S⁻¹ :=
  Homeomorph.ext fun y => by rw [h, Homeomorph.inv_apply]

theorem forall_apply_eq_symm_symm {S S' : Y ≃ₜ Y} (h : ∀ y, S' y = S.symm y) :
    ∀ y, S y = S'.symm y := fun y => by
  rw [eq_comm, S'.symm_apply_eq, h, S.symm_apply_apply]

/-- The ring homomorphism `R_S →+* R_{S'}` for `S' = S⁻¹`: `C(f) ↦ C(f)` and `u ↦ u⁻¹`. -/
noncomputable def flipRingHom (S S' : Y ≃ₜ Y) (h : ∀ y, S' y = S.symm y) :
    ClopenCrossedProduct S k →+* ClopenCrossedProduct S' k :=
  SkewMonoidAlgebra.liftNCRingHom ((coeff S' k).comp (ClopenCoeff.of S k).symm.toRingHom)
    ((Units.coeHom (ClopenCrossedProduct S' k)).comp
      ((Pestov91.CrossedProduct.unitHom (A := ClopenCoeff S' k)).comp invMonoidHom))
    fun {x y} => by
      show Pestov91.CrossedProduct.C (ClopenCoeff.of S' k ((ClopenCoeff.of S k).symm (y • x))) *
          (SkewMonoidAlgebra.single y⁻¹ 1 : ClopenCrossedProduct S' k) =
        (SkewMonoidAlgebra.single y⁻¹ 1 : ClopenCrossedProduct S' k) *
          Pestov91.CrossedProduct.C (ClopenCoeff.of S' k ((ClopenCoeff.of S k).symm x))
      rw [Pestov91.CrossedProduct.C_mul_single, mul_one, Pestov91.CrossedProduct.single_mul_C,
        one_mul]
      congr 1
      refine LocallyConstant.ext fun z => ?_
      show (ClopenCoeff.of S k).symm x ((S ^ (-toAdd y)) z) =
        (ClopenCoeff.of S k).symm x ((S' ^ (-toAdd y⁻¹)) z)
      rw [toAdd_inv, neg_neg, eq_inv_of_forall_apply_eq_symm h, inv_zpow']

theorem flipRingHom_apply (S S' : Y ≃ₜ Y) (h : ∀ y, S' y = S.symm y) (x : ClopenCrossedProduct S k) :
    flipRingHom k S S' h x = SkewMonoidAlgebra.liftNC
      (((coeff S' k).comp (ClopenCoeff.of S k).symm.toRingHom :
        ClopenCoeff S k →+* ClopenCrossedProduct S' k) : ClopenCoeff S k →+ ClopenCrossedProduct S' k)
      ((Units.coeHom (ClopenCrossedProduct S' k)).comp
        ((Pestov91.CrossedProduct.unitHom (A := ClopenCoeff S' k)).comp invMonoidHom)) x :=
  rfl

theorem flipRingHom_single (S S' : Y ≃ₜ Y) (h : ∀ y, S' y = S.symm y) (g : Multiplicative ℤ)
    (a : ClopenCoeff S k) :
    flipRingHom k S S' h (SkewMonoidAlgebra.single g a) =
      coeff S' k ((ClopenCoeff.of S k).symm a) *
        ((unit S' k ^ (-toAdd g) : (ClopenCrossedProduct S' k)ˣ) : ClopenCrossedProduct S' k) := by
  rw [flipRingHom_apply, SkewMonoidAlgebra.liftNC_single, Pestov91.CrossedProduct.val_unit_zpow,
    ofAdd_neg, ofAdd_toAdd]
  rfl

/-- `C(f) ↦ C(f)`. -/
theorem flipRingHom_coeff (S S' : Y ≃ₜ Y) (h : ∀ y, S' y = S.symm y) (f : LocallyConstant Y k) :
    flipRingHom k S S' h (coeff S k f) = coeff S' k f := by
  rw [show coeff S k f = SkewMonoidAlgebra.single 1 (ClopenCoeff.of S k f) from rfl,
    flipRingHom_single, RingEquiv.symm_apply_apply, toAdd_one, neg_zero, zpow_zero, Units.val_one,
    mul_one]

/-- `u^j ↦ u^{-j}`. -/
theorem flipRingHom_unit_zpow (S S' : Y ≃ₜ Y) (h : ∀ y, S' y = S.symm y) (j : ℤ) :
    flipRingHom k S S' h ((unit S k ^ j : (ClopenCrossedProduct S k)ˣ) : ClopenCrossedProduct S k) =
      ((unit S' k ^ (-j) : (ClopenCrossedProduct S' k)ˣ) : ClopenCrossedProduct S' k) := by
  rw [Pestov91.CrossedProduct.val_unit_zpow, flipRingHom_single, toAdd_ofAdd, map_one, map_one,
    one_mul]

/-- **The flip isomorphism** `R_S ≃+* R_{S⁻¹}`: `C(f) ↦ C(f)`, `u ↦ u⁻¹`. -/
noncomputable def flipRingEquiv (S S' : Y ≃ₜ Y) (h : ∀ y, S' y = S.symm y) :
    ClopenCrossedProduct S k ≃+* ClopenCrossedProduct S' k :=
  RingEquiv.ofRingHom (flipRingHom k S S' h) (flipRingHom k S' S (forall_apply_eq_symm_symm h))
    (ringHom_ext_coeff_unit
      (fun a => by rw [RingHom.comp_apply, flipRingHom_coeff, flipRingHom_coeff, RingHom.id_apply])
      fun j => by
        rw [RingHom.comp_apply, flipRingHom_unit_zpow, flipRingHom_unit_zpow, neg_neg,
          RingHom.id_apply])
    (ringHom_ext_coeff_unit
      (fun a => by rw [RingHom.comp_apply, flipRingHom_coeff, flipRingHom_coeff, RingHom.id_apply])
      fun j => by
        rw [RingHom.comp_apply, flipRingHom_unit_zpow, flipRingHom_unit_zpow, neg_neg,
          RingHom.id_apply])

end Flip

section Groups

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y}
  (k : Type*) [Ring k]

/-- **Conjugate or flip conjugate systems have isomorphic crossed products.** -/
theorem nonempty_ringEquiv_of_conj_or_flip (φ : X ≃ₜ Y)
    (hφ : (∀ x, φ (T x) = S (φ x)) ∨ ∀ x, φ (T x) = S.symm (φ x)) :
    Nonempty (ClopenCrossedProduct T k ≃+* ClopenCrossedProduct S k) := by
  rcases hφ with hφ | hφ
  · exact ⟨conjRingEquiv k φ hφ⟩
  · exact ⟨(conjRingEquiv k (S := S.symm) φ hφ).trans (flipRingEquiv k S.symm S fun _ => rfl)⟩

/-- **Conjugate or flip conjugate systems have isomorphic elementary groups**, in every rank. -/
theorem nonempty_elementaryGroup_equiv_of_conj_or_flip (n : ℕ) (φ : X ≃ₜ Y)
    (hφ : (∀ x, φ (T x) = S (φ x)) ∨ ∀ x, φ (T x) = S.symm (φ x)) :
    Nonempty (elementaryGroup (Fin n) (ClopenCrossedProduct T k) ≃*
      elementaryGroup (Fin n) (ClopenCrossedProduct S k)) :=
  (nonempty_ringEquiv_of_conj_or_flip k φ hφ).map fun e => elementaryCoefficientEquiv (ι := Fin n) e

end Groups

/-- **"If $(X,T)$ is topologically conjugate to $(Y,S)$ or to $(Y,S^{-1})$, then
$G_X\cong G_Y$"** ("Questions"), for subshifts with `G_X = EL₃(LC(X, F₂) ⋊_T ℤ)`. -/
def PrintedConjugacyIsomorphism : Prop :=
  ∀ (A B : Type) [TopologicalSpace A] [TopologicalSpace B] (S : Subshift A ℤ) (S' : Subshift B ℤ)
    (φ : S.carrier ≃ₜ S'.carrier),
    ((∀ x, φ (subshiftHomeo S x) = subshiftHomeo S' (φ x)) ∨
      ∀ x, φ (subshiftHomeo S x) = (subshiftHomeo S').symm (φ x)) →
    Nonempty (G S ≃* G S')

theorem printedConjugacyIsomorphism : PrintedConjugacyIsomorphism :=
  fun _ _ _ _ _ _ φ hφ => nonempty_elementaryGroup_equiv_of_conj_or_flip (ZMod 2) 3 φ hφ

end SimpleKazhdanSofic

end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.conjRingEquiv
#audit_axioms GroupApproximation.SimpleKazhdanSofic.flipRingEquiv
#audit_axioms GroupApproximation.SimpleKazhdanSofic.nonempty_elementaryGroup_equiv_of_conj_or_flip
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedConjugacyIsomorphism
