import GroupApproximation.Dynamics.ClopenCrossedProduct
import GroupApproximation.Algebra.SkewMonoidAlgebraCoefficientMap
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Pullback of clopen crossed products; restriction to an invariant set

`non_mf_groups_exist.tex`, proof of `lem:chain-core-models`.  Clopen data is pulled back along
factor maps, and `R_X` restricts to the ring `R_Y` of an invariant set (tex 1460: "Restriction to
the directly finite ring $R_Y$ forces $d|_Y=0$").

For homeomorphisms `T : X ≃ₜ X`, `S : Z ≃ₜ Z` and a continuous `π : X → Z` with `π ∘ T = S ∘ π`:

* `semiconj_zpow`: `π ∘ T ^ n = S ^ n ∘ π` for every `n : ℤ`;
* `coeffComap T S k π : ClopenCoeff S k →+* ClopenCoeff T k`, `f ↦ f ∘ π`, which is equivariant
  (`coeffComap_smul`);
* `comap k π hπ : ClopenCrossedProduct S k →+* ClopenCrossedProduct T k`, the coefficient map
  `Pestov91.CrossedProduct.coeffMap` along `coeffComap`, with `comap_coeff : C(f) ↦ C(f ∘ π)`,
  `comap_unit_zpow : u ^ j ↦ u ^ j` and `comap_unit`;
* `coeff_injective`: `LC(X, k) → R_X` is injective;
* for `T '' Y = Y`: `restrictHomeo T hY : Y ≃ₜ Y`, and the restriction `restrict T k hY : R_X →+* R_Y`
  (`comap` along the inclusion), with `restrict_coeff : C(f) ↦ C(f|_Y)` and `restrict_unit`.
-/

namespace GroupApproximation

open Multiplicative (toAdd)

namespace ClopenCrossedProduct

section Comap

variable {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] {T : X ≃ₜ X} {S : Z ≃ₜ Z}

/-- A semiconjugacy `π ∘ T = S ∘ π` intertwines all integer powers. -/
theorem semiconj_zpow {π : X → Z} (h : ∀ x, π (T x) = S (π x)) (n : ℤ) :
    ∀ x, π ((T ^ n) x) = (S ^ n) (π x) := by
  have hsymm : ∀ x, π (T.symm x) = S.symm (π x) := fun x => by
    rw [eq_comm, S.symm_apply_eq, ← h, T.apply_symm_apply]
  induction n with
  | zero =>
    intro x
    rw [zpow_zero, zpow_zero, Homeomorph.one_apply, Homeomorph.one_apply]
  | succ i ih =>
    intro x
    rw [zpow_add_one, zpow_add_one, Homeomorph.mul_apply, Homeomorph.mul_apply, ih, h]
  | pred i ih =>
    intro x
    rw [zpow_sub_one, zpow_sub_one, Homeomorph.mul_apply, Homeomorph.mul_apply,
      Homeomorph.inv_apply, Homeomorph.inv_apply, ih, hsymm]

variable (k : Type*) [Ring k]

variable (T S) in
/-- Pulling coefficients back along `π`: `f ↦ f ∘ π`. -/
noncomputable def coeffComap (π : C(X, Z)) : ClopenCoeff S k →+* ClopenCoeff T k :=
  RingHom.comp (ClopenCoeff.of T k).toRingHom
    (RingHom.comp (LocallyConstant.comapRingHom π) (ClopenCoeff.of S k).symm.toRingHom)

@[simp]
theorem coeffComap_of (π : C(X, Z)) (f : LocallyConstant Z k) :
    coeffComap T S k π (ClopenCoeff.of S k f) = ClopenCoeff.of T k (LocallyConstant.comap π f) :=
  rfl

/-- `coeffComap` intertwines the two `ℤ`-actions. -/
theorem coeffComap_smul (π : C(X, Z)) (hπ : ∀ x, π (T x) = S (π x)) (j : Multiplicative ℤ)
    (a : ClopenCoeff S k) : coeffComap T S k π (j • a) = j • coeffComap T S k π a :=
  LocallyConstant.ext fun x => by
    show (ClopenCoeff.of S k).symm a ((S ^ (-toAdd j)) (π x)) =
      (ClopenCoeff.of S k).symm a (π ((T ^ (-toAdd j)) x))
    rw [semiconj_zpow hπ]

/-- **Pullback along a semiconjugacy.**  For continuous `π` with `π ∘ T = S ∘ π`, the unital ring
map `R_S → R_T` with `C(f) ↦ C(f ∘ π)` and `u ↦ u`. -/
noncomputable def comap (π : C(X, Z)) (hπ : ∀ x, π (T x) = S (π x)) :
    ClopenCrossedProduct S k →+* ClopenCrossedProduct T k :=
  Pestov91.CrossedProduct.coeffMap (coeffComap T S k π) (coeffComap_smul k π hπ)

/-- `comap` sends `C(f)` to `C(f ∘ π)`. -/
theorem comap_coeff (π : C(X, Z)) (hπ : ∀ x, π (T x) = S (π x)) (f : LocallyConstant Z k) :
    comap k π hπ (coeff S k f) = coeff T k (LocallyConstant.comap π f) := by
  simp only [comap, coeff_apply, Pestov91.CrossedProduct.coeffMap_C, coeffComap_of]

/-- `comap` sends `u ^ j` to `u ^ j`. -/
theorem comap_unit_zpow (π : C(X, Z)) (hπ : ∀ x, π (T x) = S (π x)) (j : ℤ) :
    comap k π hπ ((unit S k ^ j : (ClopenCrossedProduct S k)ˣ) : ClopenCrossedProduct S k) =
      ((unit T k ^ j : (ClopenCrossedProduct T k)ˣ) : ClopenCrossedProduct T k) := by
  simp only [comap, Pestov91.CrossedProduct.val_unit_zpow, Pestov91.CrossedProduct.coeffMap_single,
    map_one]

/-- `comap` sends `u` to `u`. -/
theorem comap_unit (π : C(X, Z)) (hπ : ∀ x, π (T x) = S (π x)) :
    comap k π hπ (unit S k : ClopenCrossedProduct S k) = (unit T k : ClopenCrossedProduct T k) := by
  simpa only [zpow_one] using comap_unit_zpow k π hπ 1

end Comap

section Restrict

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type*) [Ring k] {Y : Set X}

/-- The coefficient embedding `LC(X, k) → R_X` is injective. -/
theorem coeff_injective : Function.Injective (coeff T k) := by
  intro a b h
  rw [coeff_apply, coeff_apply, Pestov91.CrossedProduct.C_apply,
    Pestov91.CrossedProduct.C_apply] at h
  exact (ClopenCoeff.of T k).injective (SkewMonoidAlgebra.single_injective _ h)

theorem mem_iff_apply_mem (hY : T '' Y = Y) (x : X) : x ∈ Y ↔ T x ∈ Y := by
  constructor
  · intro hx
    rw [← hY]
    exact Set.mem_image_of_mem T hx
  · intro hx
    rw [← hY] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← T.injective hyx]

/-- `T|_Y : Y ≃ₜ Y` for an invariant set `T(Y) = Y`. -/
def restrictHomeo (hY : T '' Y = Y) : Y ≃ₜ Y :=
  T.subtype (mem_iff_apply_mem T hY)

theorem restrictHomeo_apply (hY : T '' Y = Y) (y : Y) : (restrictHomeo T hY y : X) = T y :=
  rfl

/-- **Restriction** `R_X → R_Y` to an invariant set `Y`: `C(f) ↦ C(f|_Y)` and `u ↦ u`. -/
noncomputable def restrict (hY : T '' Y = Y) :
    ClopenCrossedProduct T k →+* ClopenCrossedProduct (restrictHomeo T hY) k :=
  comap (T := restrictHomeo T hY) (S := T) k ⟨Subtype.val, continuous_subtype_val⟩ fun _ => rfl

theorem restrict_coeff (hY : T '' Y = Y) (f : LocallyConstant X k) :
    restrict T k hY (coeff T k f) =
      coeff (restrictHomeo T hY) k
        (LocallyConstant.comap ⟨Subtype.val, continuous_subtype_val⟩ f) :=
  comap_coeff k _ _ f

theorem restrict_unit (hY : T '' Y = Y) :
    restrict T k hY (unit T k : ClopenCrossedProduct T k) =
      (unit (restrictHomeo T hY) k : ClopenCrossedProduct (restrictHomeo T hY) k) :=
  comap_unit k _ _

end Restrict

end ClopenCrossedProduct

end GroupApproximation

open GroupApproximation

#audit_axioms GroupApproximation.ClopenCrossedProduct.comap_coeff
#audit_axioms GroupApproximation.ClopenCrossedProduct.comap_unit
#audit_axioms GroupApproximation.ClopenCrossedProduct.restrict_coeff
#audit_axioms GroupApproximation.ClopenCrossedProduct.restrict_unit
#audit_axioms GroupApproximation.ClopenCrossedProduct.coeff_injective
