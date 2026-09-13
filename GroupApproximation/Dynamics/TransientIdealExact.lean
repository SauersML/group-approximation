import GroupApproximation.Dynamics.ClopenCrossedProductComap
import GroupApproximation.Meta.AxiomGuard
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.Topology.Separation.Profinite

/-!
# The transient ideal: the kernel of the restriction `R_X → R_Y`

`non_mf_groups_exist.tex`, lem:transient-matrices (tex 1468–1480).  For a closed invariant set
`Y ⊆ X`, restriction `R_X → R_Y` is chain-core's `restrict T k hY`, and
`I = ker (R_X → R_Y)` is the transient ideal.

* `transientIdeal T k hY`: the two-sided ideal `ker (restrict T k hY)`; `mem_transientIdeal`.
* `coeff_restrict`: the Laurent coefficients of the restriction are the restricted coefficients.
* `mem_transientIdeal_iff_forall_coeff`: `x ∈ I` iff every Laurent coefficient of `x` vanishes on
  `Y` (tex 1480, "Laurent normal forms give exactness").
* `restrict_injective_iff`, `transientIdeal_eq_bot_iff`: `I = ⊥ ↔ Y = X`, for nontrivial `k`.
-/

namespace GroupApproximation
namespace ClopenCrossedProduct

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type*) [Ring k] {Y : Set X}

/-- The transient ideal `I = ker (R_X → R_Y)` of a closed invariant set `Y` (tex 1468). -/
noncomputable def transientIdeal (hY : T '' Y = Y) : TwoSidedIdeal (ClopenCrossedProduct T k) :=
  TwoSidedIdeal.ker (restrict T k hY)

theorem mem_transientIdeal (hY : T '' Y = Y) {x : ClopenCrossedProduct T k} :
    x ∈ transientIdeal T k hY ↔ restrict T k hY x = 0 :=
  TwoSidedIdeal.mem_ker _

/-- The Laurent coefficients of the restriction are the restricted coefficients. -/
theorem coeff_restrict (hY : T '' Y = Y) (x : ClopenCrossedProduct T k) (g : Multiplicative ℤ) :
    SkewMonoidAlgebra.coeff (restrict T k hY x) g =
      coeffComap (restrictHomeo T hY) T k ⟨Subtype.val, continuous_subtype_val⟩
        (SkewMonoidAlgebra.coeff x g) :=
  Pestov91.CrossedProduct.coeff_coeffMap _
    (coeffComap_smul (T := restrictHomeo T hY) (S := T) k ⟨Subtype.val, continuous_subtype_val⟩
      fun _ => rfl) x g

/-- **Exactness in the middle** (tex 1480): `x ∈ I` iff every Laurent coefficient of `x` vanishes
on `Y`. -/
theorem mem_transientIdeal_iff_forall_coeff (hY : T '' Y = Y) {x : ClopenCrossedProduct T k} :
    x ∈ transientIdeal T k hY ↔
      ∀ (g : Multiplicative ℤ), ∀ y ∈ Y,
        (ClopenCoeff.of T k).symm (SkewMonoidAlgebra.coeff x g) y = 0 := by
  rw [mem_transientIdeal, SkewMonoidAlgebra.ext_iff]
  refine forall_congr' fun g => ?_
  rw [coeff_restrict, SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  constructor
  · intro h y hy
    exact LocallyConstant.congr_fun
      (congrArg (ClopenCoeff.of (restrictHomeo T hY) k).symm h) ⟨y, hy⟩
  · intro h
    exact LocallyConstant.ext fun y => h y y.2

/-- Restriction to all of `X` is injective. -/
theorem restrict_injective_of_eq_univ (hY : T '' Y = Y) (hYu : Y = Set.univ) :
    Function.Injective (restrict T k hY) := by
  refine Pestov91.CrossedProduct.coeffMap_injective _
    (coeffComap_smul (T := restrictHomeo T hY) (S := T) k ⟨Subtype.val, continuous_subtype_val⟩
      fun _ => rfl) fun a b hab => ?_
  refine LocallyConstant.ext fun x => ?_
  have hx : x ∈ Y := by rw [hYu]; exact Set.mem_univ x
  exact LocallyConstant.congr_fun
    (congrArg (ClopenCoeff.of (restrictHomeo T hY) k).symm hab) ⟨x, hx⟩

/-- A proper closed invariant set has a nonzero element of `R_X` restricting to `0`: the indicator
of a clopen neighbourhood of a point outside `Y` that misses `Y`. -/
theorem eq_univ_of_restrict_injective [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [Nontrivial k] (hYc : IsClosed Y) (hY : T '' Y = Y)
    (hinj : Function.Injective (restrict T k hY)) : Y = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  by_contra hx
  obtain ⟨V, hV, hxV, hVY⟩ := compact_exists_isClopen_in_isOpen hYc.isOpen_compl hx
  have hcomap : LocallyConstant.comap (⟨Subtype.val, continuous_subtype_val⟩ : C(Y, X))
      (LocallyConstant.charFn k hV) = (0 : LocallyConstant Y k) :=
    LocallyConstant.ext fun y =>
      (LocallyConstant.charFn_eq_zero k (y : X) hV).2 fun hyV => hVY hyV y.2
  have h0 : restrict T k hY (coeff T k (LocallyConstant.charFn k hV)) = restrict T k hY 0 := by
    rw [restrict_coeff, hcomap, map_zero, map_zero]
  have h1 : LocallyConstant.charFn k hV = 0 :=
    coeff_injective T k ((hinj h0).trans (map_zero (coeff T k)).symm)
  exact (LocallyConstant.charFn_eq_zero k x hV).1 (LocallyConstant.congr_fun h1 x) hxV

theorem restrict_injective_iff [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [Nontrivial k] (hYc : IsClosed Y) (hY : T '' Y = Y) :
    Function.Injective (restrict T k hY) ↔ Y = Set.univ :=
  ⟨eq_univ_of_restrict_injective T k hYc hY, restrict_injective_of_eq_univ T k hY⟩

/-- `I = ⊥` exactly when `Y = X` (for nontrivial `k`). -/
theorem transientIdeal_eq_bot_iff [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [Nontrivial k] (hYc : IsClosed Y) (hY : T '' Y = Y) :
    transientIdeal T k hY = ⊥ ↔ Y = Set.univ := by
  rw [transientIdeal, TwoSidedIdeal.ker_eq_bot]
  exact restrict_injective_iff T k hYc hY

end ClopenCrossedProduct
end GroupApproximation

open GroupApproximation

#audit_axioms GroupApproximation.ClopenCrossedProduct.mem_transientIdeal_iff_forall_coeff
#audit_axioms GroupApproximation.ClopenCrossedProduct.transientIdeal_eq_bot_iff
