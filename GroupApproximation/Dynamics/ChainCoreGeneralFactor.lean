import GroupApproximation.Dynamics.OneBlockCycleCondition
import GroupApproximation.Dynamics.ClopenCrossedProductComap
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The itinerary factors of the general core

`non_mf_groups_exist.tex`, proof of Lemma `lem:chain-core-models` (tex lines 1442–1445):

> Coefficient pullback gives injective unital maps of crossed products, and every locally constant
> function is constant on a sufficiently fine partition.  Thus $R_{Y_*}$ is an increasing union of LEF
> rings and is LEF.

For clopen partitions `S m` of `X` and the inverse-limit core `Y_* = generalCore T S`, this module
supplies the maps of that sentence.

* `image_generalCore`: `T(Y_*) = Y_*`, so `T` restricts to `Y_*` (`ClopenCrossedProduct.restrictHomeo`).
* `coreFactor T S m = π_m(Y_*)` is shift-invariant (`mapsTo_shift_coreFactor`), closed over compact `X`
  (`isClosed_coreFactor`), with the shift `coreFactorShift`.
* `coreFactorMap : Y_* → π_m(Y_*)` is continuous, surjective, and intertwines `T|_{Y_*}` with the shift
  (`coreFactorMap_semiconj`).
* `comap_injective`: pulling coefficients back along a surjective factor map is injective.
* `range_comap_coreFactorMap_mono`: the pulled-back rings increase with `m`, through the one-block maps
  `coreFactorOneBlock`.

## Manuscript status

Infrastructure for `lem:chain-core-models` (tex 1371); certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace ChainCore

open Set SymbolicDynamics.FullShift GroupApproximation.WordGraph

section FullShift

variable {A : Type*} [TopologicalSpace A]

/-- The shift by one on the full shift `A^ℤ`, as a homeomorphism. -/
def fullShiftHomeomorph : (ℤ → A) ≃ₜ (ℤ → A) where
  toFun := shift 1
  invFun := shift (-1)
  left_inv x := by
    funext i
    simp only [shift_apply, add_neg_cancel_left]
  right_inv x := by
    funext i
    simp only [shift_apply, neg_add_cancel_left]
  continuous_toFun := continuous_shift 1
  continuous_invFun := continuous_shift (-1)

theorem fullShiftHomeomorph_apply (x : ℤ → A) : fullShiftHomeomorph x = shift 1 x :=
  rfl

omit [TopologicalSpace A] in
theorem shift_neg_one_shift_one (x : ℤ → A) : shift (-1) (shift 1 x) = x := by
  funext i
  simp only [shift_apply, add_neg_cancel_left]

end FullShift

section Factor

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X)

/-- The itinerary of `T⁻¹ x` is the itinerary of `x` shifted back by one. -/
theorem itinerary_symm_apply (S : DiscreteQuotient X) (x : X) :
    itinerary T S (T.symm x) = shift (-1) (itinerary T S x) := by
  have h := itinerary_apply_self T S (T.symm x)
  rw [Homeomorph.apply_symm_apply] at h
  rw [h, shift_neg_one_shift_one]

/-- The zero coordinate of an itinerary is the atom of the point. -/
theorem itinerary_apply_zero (S : DiscreteQuotient X) (x : X) :
    itinerary T S x 0 = S.proj x := by
  rw [itinerary_apply, zpow_zero]
  rfl

variable (S : ℕ → DiscreteQuotient X)

/-- `T(Y_*) = Y_*`. -/
theorem image_generalCore : T '' generalCore T S = generalCore T S := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine (mem_inverseLimitCore T).2 fun m ↦ ?_
    rw [itinerary_apply_self]
    exact mapsTo_shift_itineraryCore T (S m) 1 ((mem_inverseLimitCore T).1 hx m)
  · intro hy
    refine ⟨T.symm y, (mem_inverseLimitCore T).2 fun m ↦ ?_, T.apply_symm_apply y⟩
    rw [itinerary_symm_apply]
    exact mapsTo_shift_itineraryCore T (S m) (-1) ((mem_inverseLimitCore T).1 hy m)

/-- The factor `π_m(Y_*)` of the general core. -/
abbrev coreFactor (m : ℕ) : Set (ℤ → S m) :=
  itinerary T (S m) '' generalCore T S

theorem mapsTo_shift_coreFactor (m : ℕ) (n : ℤ) :
    MapsTo (shift n) (coreFactor T S m) (coreFactor T S m) := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨(T ^ n) y, mapsTo_zpow_generalCore T S n hy, itinerary_zpow_apply T (S m) n y⟩

theorem isClosed_coreFactor [CompactSpace X] (m : ℕ) : IsClosed (coreFactor T S m) :=
  ((isClosed_generalCore T S).isCompact.image (continuous_itinerary T (S m))).isClosed

theorem mem_coreFactor_iff_shift (m : ℕ) (z : ℤ → S m) :
    z ∈ coreFactor T S m ↔ fullShiftHomeomorph z ∈ coreFactor T S m := by
  refine ⟨fun h ↦ mapsTo_shift_coreFactor T S m 1 h, fun h ↦ ?_⟩
  have h' := mapsTo_shift_coreFactor T S m (-1) h
  rwa [fullShiftHomeomorph_apply, shift_neg_one_shift_one] at h'

/-- The shift on `π_m(Y_*)`. -/
def coreFactorShift (m : ℕ) : coreFactor T S m ≃ₜ coreFactor T S m :=
  Homeomorph.subtype (p := (· ∈ coreFactor T S m)) (q := (· ∈ coreFactor T S m))
    fullShiftHomeomorph (mem_coreFactor_iff_shift T S m)

theorem coreFactorShift_apply (m : ℕ) (z : coreFactor T S m) :
    (coreFactorShift T S m z : ℤ → S m) = shift 1 (z : ℤ → S m) :=
  rfl

/-- The factor map `π_m : Y_* → π_m(Y_*)`. -/
def coreFactorMap (m : ℕ) : C(generalCore T S, coreFactor T S m) where
  toFun y := ⟨itinerary T (S m) y, y, y.2, rfl⟩
  continuous_toFun :=
    ((continuous_itinerary T (S m)).comp continuous_subtype_val).subtype_mk _

theorem coreFactorMap_apply (m : ℕ) (y : generalCore T S) :
    (coreFactorMap T S m y : ℤ → S m) = itinerary T (S m) y :=
  rfl

theorem coreFactorMap_surjective (m : ℕ) : Function.Surjective (coreFactorMap T S m) := by
  rintro ⟨_, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

/-- `π_m` intertwines `T|_{Y_*}` with the shift. -/
theorem coreFactorMap_semiconj (m : ℕ) (y : generalCore T S) :
    coreFactorMap T S m (ClopenCrossedProduct.restrictHomeo T (image_generalCore T S) y) =
      coreFactorShift T S m (coreFactorMap T S m y) :=
  Subtype.ext (itinerary_apply_self T (S m) y)

end Factor

section Pullback

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] {TY : Y ≃ₜ Y} {TZ : Z ≃ₜ Z}
  (k : Type*) [Ring k]

theorem coeffComap_injective (π : C(Y, Z)) (hsurj : Function.Surjective π) :
    Function.Injective (ClopenCrossedProduct.coeffComap TY TZ k π) := by
  intro a b hab
  obtain ⟨f, rfl⟩ := (ClopenCoeff.of TZ k).surjective a
  obtain ⟨g, rfl⟩ := (ClopenCoeff.of TZ k).surjective b
  rw [ClopenCrossedProduct.coeffComap_of, ClopenCrossedProduct.coeffComap_of] at hab
  have hfg := (ClopenCoeff.of TY k).injective hab
  congr 1
  refine LocallyConstant.ext fun z ↦ ?_
  obtain ⟨y, rfl⟩ := hsurj z
  exact congrArg (fun h : LocallyConstant Y k ↦ h y) hfg

/-- **Coefficient pullback along a surjective factor map is injective.** -/
theorem comap_injective (π : C(Y, Z)) (hπ : ∀ y, π (TY y) = TZ (π y))
    (hsurj : Function.Surjective π) :
    Function.Injective (ClopenCrossedProduct.comap k π hπ) := by
  apply Pestov91.CrossedProduct.coeffMap_injective
  exact coeffComap_injective k π hsurj

/-- `comap` on a Laurent sum. -/
theorem comap_sum_coeff_mul_unit_zpow (π : C(Y, Z)) (hπ : ∀ y, π (TY y) = TZ (π y))
    (J : Finset ℤ) (f : ℤ → LocallyConstant Z k) :
    ClopenCrossedProduct.comap k π hπ
        (∑ j ∈ J, ClopenCrossedProduct.coeff TZ k (f j) *
          ((ClopenCrossedProduct.unit TZ k ^ j : (ClopenCrossedProduct TZ k)ˣ) :
            ClopenCrossedProduct TZ k)) =
      ∑ j ∈ J, ClopenCrossedProduct.coeff TY k (LocallyConstant.comap π (f j)) *
        ((ClopenCrossedProduct.unit TY k ^ j : (ClopenCrossedProduct TY k)ˣ) :
          ClopenCrossedProduct TY k) := by
  simp only [map_sum, map_mul, ClopenCrossedProduct.comap_coeff,
    ClopenCrossedProduct.comap_unit_zpow]

end Pullback

section Mono

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) {S : ℕ → DiscreteQuotient X}

theorem oneBlock_mem_coreFactor (hS : Antitone S) {m l : ℕ} (h : m ≤ l) {z : ℤ → S l}
    (hz : z ∈ coreFactor T S l) : oneBlock (hS h) z ∈ coreFactor T S m := by
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨y, hy, (oneBlock_itinerary (T := T) (hS h) y).symm⟩

/-- The one-block map `π_l(Y_*) → π_m(Y_*)` for `m ≤ l`. -/
def coreFactorOneBlock (hS : Antitone S) {m l : ℕ} (h : m ≤ l) :
    C(coreFactor T S l, coreFactor T S m) where
  toFun z := ⟨oneBlock (hS h) z, oneBlock_mem_coreFactor T hS h z.2⟩
  continuous_toFun :=
    ((continuous_oneBlock (hS h)).comp continuous_subtype_val).subtype_mk _

theorem coreFactorOneBlock_comp (hS : Antitone S) {m l : ℕ} (h : m ≤ l) (y : generalCore T S) :
    coreFactorOneBlock T hS h (coreFactorMap T S l y) = coreFactorMap T S m y :=
  Subtype.ext (oneBlock_itinerary (T := T) (hS h) y)

variable (k : Type*) [Ring k]

/-- **The pulled-back rings increase with `m`**: `C(f) u^j` pulled back along `π_m` is `C(f ∘ ρ) u^j`
pulled back along `π_l`. -/
theorem range_comap_coreFactorMap_mono (hS : Antitone S) {m l : ℕ} (h : m ≤ l) :
    (ClopenCrossedProduct.comap k (coreFactorMap T S m) (coreFactorMap_semiconj T S m)).range ≤
      (ClopenCrossedProduct.comap k (coreFactorMap T S l) (coreFactorMap_semiconj T S l)).range := by
  intro a ha
  obtain ⟨b, rfl⟩ := RingHom.mem_range.1 ha
  obtain ⟨J, f, rfl⟩ :=
    ClopenCrossedProduct.exists_sum_coeff_mul_unit_zpow (coreFactorShift T S m) k b
  refine RingHom.mem_range.2
    ⟨∑ j ∈ J, ClopenCrossedProduct.coeff (coreFactorShift T S l) k
      (LocallyConstant.comap (coreFactorOneBlock T hS h) (f j)) *
      ((ClopenCrossedProduct.unit (coreFactorShift T S l) k ^ j :
        (ClopenCrossedProduct (coreFactorShift T S l) k)ˣ) :
        ClopenCrossedProduct (coreFactorShift T S l) k), ?_⟩
  rw [comap_sum_coeff_mul_unit_zpow, comap_sum_coeff_mul_unit_zpow]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hf : LocallyConstant.comap (coreFactorMap T S l)
      (LocallyConstant.comap (coreFactorOneBlock T hS h) (f j)) =
        LocallyConstant.comap (coreFactorMap T S m) (f j) :=
    LocallyConstant.ext fun y ↦ congrArg (f j) (coreFactorOneBlock_comp T hS h y)
  rw [hf]

end Mono

end ChainCore
end GroupApproximation

#audit_axioms GroupApproximation.ChainCore.image_generalCore
#audit_axioms GroupApproximation.ChainCore.isClosed_coreFactor
#audit_axioms GroupApproximation.ChainCore.coreFactorMap_surjective
#audit_axioms GroupApproximation.ChainCore.coreFactorMap_semiconj
#audit_axioms GroupApproximation.ChainCore.comap_injective
#audit_axioms GroupApproximation.ChainCore.range_comap_coreFactorMap_mono
