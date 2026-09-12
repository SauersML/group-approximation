import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import GroupApproximation.Meta.AxiomGuard

/-!
# From `ℤᵐ⁰`-valued valuations to additive valuations in `WithTop ℤ`

The Bruhat--Tits tree step of the remark after `prop:torsion-defect-ring` of
`non_mf_groups_exist.tex` (tex lines 1146--1147) is stated for a field `K` with an additive
discrete valuation `v : AddValuation K (WithTop ℤ)` and a uniformizer `v π = 1`
(`Algebra/ValuedMatrixTwo`, `Kazhdan/BruhatTitsTwoTree`).  Mathlib's places of global fields
(`IsDedekindDomain.HeightOneSpectrum.valuation`, `RatFunc.inftyValuation`) are multiplicative
valuations `K → ℤᵐ⁰` with uniformizers of value `exp (-1)`.  This module converts one into the
other.

For `w : Valuation K ℤᵐ⁰` put `addVal w x = -log (w x)` for `x ≠ 0` and `addVal w 0 = ⊤`.

* `addVal w` is an additive valuation (`addVal`), with `addVal w x = -log (w x)` off zero
  (`addVal_of_ne_zero`);
* an element of value `exp (-1)` is a uniformizer: `addVal w π = 1` (`addVal_eq_one`);
* lower bounds for `addVal w` are upper bounds for `w`: `-N ≤ addVal w x ↔ w x ≤ exp N`
  (`neg_le_addVal_iff`).
-/

namespace GroupApproximation
namespace ValuationWithTopInt

open WithZero

variable {K : Type*} [Field K] (w : Valuation K ℤᵐ⁰)

/-- The underlying function of `addVal w`. -/
noncomputable def addValFun (x : K) : WithTop ℤ :=
  haveI := Classical.dec (x = 0)
  if x = 0 then ⊤ else ((-log (w x) : ℤ) : WithTop ℤ)

theorem addValFun_zero : addValFun w 0 = ⊤ := by
  simp [addValFun]

theorem addValFun_of_ne_zero {x : K} (hx : x ≠ 0) :
    addValFun w x = ((-log (w x) : ℤ) : WithTop ℤ) := by
  simp [addValFun, hx]

theorem addValFun_one : addValFun w 1 = 0 := by
  rw [addValFun_of_ne_zero w one_ne_zero, Valuation.map_one, log_one, neg_zero]
  rfl

theorem addValFun_mul (x y : K) : addValFun w (x * y) = addValFun w x + addValFun w y := by
  by_cases hx : x = 0
  · rw [hx, zero_mul, addValFun_zero, WithTop.top_add]
  by_cases hy : y = 0
  · rw [hy, mul_zero, addValFun_zero, WithTop.add_top]
  have hwx : w x ≠ 0 := (Valuation.ne_zero_iff w).mpr hx
  have hwy : w y ≠ 0 := (Valuation.ne_zero_iff w).mpr hy
  rw [addValFun_of_ne_zero w (mul_ne_zero hx hy), addValFun_of_ne_zero w hx,
    addValFun_of_ne_zero w hy, Valuation.map_mul, log_mul hwx hwy, neg_add, WithTop.coe_add]

theorem addValFun_add (x y : K) : min (addValFun w x) (addValFun w y) ≤ addValFun w (x + y) := by
  by_cases hxy : x + y = 0
  · rw [hxy, addValFun_zero]
    exact le_top
  by_cases hx : x = 0
  · rw [hx, zero_add, addValFun_zero]
    exact min_le_right _ _
  by_cases hy : y = 0
  · rw [hy, add_zero, addValFun_zero]
    exact min_le_left _ _
  have hwx : w x ≠ 0 := (Valuation.ne_zero_iff w).mpr hx
  have hwy : w y ≠ 0 := (Valuation.ne_zero_iff w).mpr hy
  have hwxy : w (x + y) ≠ 0 := (Valuation.ne_zero_iff w).mpr hxy
  rw [addValFun_of_ne_zero w hx, addValFun_of_ne_zero w hy, addValFun_of_ne_zero w hxy]
  have hmax := Valuation.map_add w x y
  rcases le_total (w x) (w y) with h | h
  · rw [max_eq_right h] at hmax
    have hlog : log (w (x + y)) ≤ log (w y) := (log_le_log hwxy hwy).mpr hmax
    refine (min_le_right _ _).trans ?_
    exact WithTop.coe_le_coe.mpr (by omega)
  · rw [max_eq_left h] at hmax
    have hlog : log (w (x + y)) ≤ log (w x) := (log_le_log hwxy hwx).mpr hmax
    refine (min_le_left _ _).trans ?_
    exact WithTop.coe_le_coe.mpr (by omega)

/-- **The additive valuation of a `ℤᵐ⁰`-valued valuation.** -/
noncomputable def addVal : AddValuation K (WithTop ℤ) :=
  AddValuation.of (addValFun w) (addValFun_zero w) (addValFun_one w) (addValFun_add w)
    (addValFun_mul w)

theorem addVal_apply (x : K) : addVal w x = addValFun w x :=
  rfl

theorem addVal_of_ne_zero {x : K} (hx : x ≠ 0) :
    addVal w x = ((-log (w x) : ℤ) : WithTop ℤ) := by
  rw [addVal_apply, addValFun_of_ne_zero w hx]

/-- **Uniformizers.**  An element of value `exp (-1)` has additive valuation `1`. -/
theorem addVal_eq_one {π : K} (hπ : w π = exp (-1 : ℤ)) : addVal w π = 1 := by
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hπ
    exact (exp_ne_zero (a := (-1 : ℤ))) hπ.symm
  rw [addVal_of_ne_zero w hπ0, hπ, log_exp, neg_neg]
  rfl

/-- **Lower bounds for the additive valuation are upper bounds for `w`.** -/
theorem neg_le_addVal_iff {x : K} (hx : x ≠ 0) (N : ℤ) :
    ((-N : ℤ) : WithTop ℤ) ≤ addVal w x ↔ w x ≤ exp N := by
  have hwx : w x ≠ 0 := (Valuation.ne_zero_iff w).mpr hx
  rw [addVal_of_ne_zero w hx, WithTop.coe_le_coe, neg_le_neg_iff, ← log_le_iff_le_exp hwx]

end ValuationWithTopInt
end GroupApproximation

#audit_axioms GroupApproximation.ValuationWithTopInt.addVal_eq_one
#audit_axioms GroupApproximation.ValuationWithTopInt.neg_le_addVal_iff
