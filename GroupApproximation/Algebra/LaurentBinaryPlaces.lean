import GroupApproximation.Algebra.LaurentBinaryLinearMF
import GroupApproximation.Algebra.ValuedMatrixTwo
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.HahnSeries.Summable

/-!
# The two places of `F_2[z, z^{-1}]`

The rank-two remark after `prop:torsion-defect-ring` of `non_mf_groups_exist.tex`
(tex lines 1146--1150) passes from `GL_2(F_2[z,z^{-1}])` to `GL_2` over a field.  The
Bruhat--Tits argument uses the two places of the Laurent ring, at `z` and at
`z^{-1}`; this module realizes both inside the field `F_2((z))` of formal Laurent
series with its `z`-adic valuation `HahnSeries.addVal`:

* `iotaZero : F_2[z,z^{-1}] → F_2((z))`, `z ↦ z`, keeps every coefficient
  (`iotaZero_coeff`);
* `iotaInf = iotaZero ∘ invert`, `z ↦ z^{-1}`, reverses them (`iotaInf_coeff`);
* a Laurent polynomial whose images at both places have valuation at least `-N` has
  its support in `[-N, N]`, so there are finitely many of them
  (`finite_of_bounded_places`).
-/

namespace GroupApproximation
namespace JacobsonLaurent

open LaurentPolynomial

/-- The field `F_2((z))` of formal Laurent series. -/
abbrev BinaryLaurentSeries : Type := HahnSeries ℤ (ZMod 2)

/-- The `z`-adic valuation of `F_2((z))`. -/
noncomputable abbrev zVal : AddValuation BinaryLaurentSeries (WithTop ℤ) :=
  HahnSeries.addVal ℤ (ZMod 2)

/-- The uniformizer `z`. -/
noncomputable def zSeries : BinaryLaurentSeries := HahnSeries.single 1 1

theorem zSeries_ne_zero : zSeries ≠ 0 := HahnSeries.single_ne_zero one_ne_zero

theorem zVal_zSeries : zVal zSeries = 1 := by
  rw [HahnSeries.addVal_apply, zSeries, HahnSeries.orderTop_single one_ne_zero]
  rfl

theorem single_mul_single_neg (a : ℤ) :
    (HahnSeries.single a (1 : ZMod 2) : BinaryLaurentSeries) * HahnSeries.single (-a) 1 = 1 := by
  rw [HahnSeries.single_mul_single, add_neg_cancel, mul_one, HahnSeries.single_zero_one]

theorem zSeries_zpow (n : ℤ) : zSeries ^ n = HahnSeries.single n 1 := by
  refine Int.induction_on n ?_ ?_ ?_
  · rw [zpow_zero, HahnSeries.single_zero_one]
  · intro k ih
    rw [zpow_add_one₀ zSeries_ne_zero, ih, zSeries, HahnSeries.single_mul_single, mul_one]
  · intro k ih
    rw [zpow_sub_one₀ zSeries_ne_zero, ih]
    have hinv : zSeries⁻¹ = HahnSeries.single (-1) 1 :=
      inv_eq_of_mul_eq_one_right (by rw [zSeries]; exact single_mul_single_neg 1)
    rw [hinv, HahnSeries.single_mul_single, mul_one, sub_eq_add_neg]

/-- `z` as a unit of `F_2((z))`. -/
noncomputable def zUnit : BinaryLaurentSeriesˣ := Units.mk0 zSeries zSeries_ne_zero

/-- **The place at `z`.** -/
noncomputable def iotaZero : BinaryLaurent →+* BinaryLaurentSeries :=
  LaurentPolynomial.eval₂ HahnSeries.C zUnit

theorem iotaZero_C_mul_T (r : ZMod 2) (n : ℤ) :
    iotaZero (C r * T n) = HahnSeries.single n r := by
  rw [iotaZero, map_mul, eval₂_C, eval₂_T, Units.val_zpow_eq_zpow_val, zUnit, Units.val_mk0,
    zSeries_zpow, HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]

/-- `iotaZero` keeps every coefficient. -/
theorem iotaZero_coeff (a : BinaryLaurent) (m : ℤ) : (iotaZero a).coeff m = a.coeff m := by
  induction a using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, HahnSeries.coeff_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  | C_mul_T n r =>
      rw [iotaZero_C_mul_T, HahnSeries.coeff_single, ← single_eq_C_mul_T,
        AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      by_cases h : m = n
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]

/-- **The place at `z^{-1}`.** -/
noncomputable def iotaInf : BinaryLaurent →+* BinaryLaurentSeries :=
  iotaZero.comp (LaurentPolynomial.invert : BinaryLaurent ≃ₐ[ZMod 2] BinaryLaurent).toRingEquiv.toRingHom

theorem iotaInf_coeff (a : BinaryLaurent) (m : ℤ) : (iotaInf a).coeff m = a.coeff (-m) := by
  show (iotaZero (LaurentPolynomial.invert a)).coeff m = _
  rw [iotaZero_coeff, invert_apply]

theorem iotaZero_ne_zero {a : BinaryLaurent} (ha : a ≠ 0) : iotaZero a ≠ 0 := by
  intro h
  apply ha
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun m ↦ ?_)
  rw [← iotaZero_coeff, h]
  rfl

theorem iotaInf_ne_zero {a : BinaryLaurent} (ha : a ≠ 0) : iotaInf a ≠ 0 := by
  intro h
  apply ha
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun m ↦ ?_)
  have := iotaInf_coeff a (-m)
  rw [h, neg_neg] at this
  exact this.symm

/-- A coefficient below the valuation vanishes. -/
theorem coeff_eq_zero_of_lt_vz {x : BinaryLaurentSeries} (hx : x ≠ 0) {m : ℤ}
    (hm : m < ValuedMatrixTwo.vz zVal x) : x.coeff m = 0 := by
  by_contra h
  have hle := HahnSeries.addVal_le_of_coeff_ne_zero h
  rw [← ValuedMatrixTwo.coe_vz zVal hx] at hle
  have : ValuedMatrixTwo.vz zVal x ≤ m := by exact_mod_cast hle
  omega

/-- **Bounded valuation at both places confines the support to `[-N, N]`.** -/
theorem coeff_eq_zero_of_bounded_places {N : ℤ} {a : BinaryLaurent} (ha : a ≠ 0)
    (h0 : -N ≤ ValuedMatrixTwo.vz zVal (iotaZero a)) (hinf : -N ≤ ValuedMatrixTwo.vz zVal (iotaInf a))
    {m : ℤ} (hm : m < -N ∨ N < m) : a.coeff m = 0 := by
  rcases hm with hm | hm
  · rw [← iotaZero_coeff]
    exact coeff_eq_zero_of_lt_vz (iotaZero_ne_zero ha) (by omega)
  · have := coeff_eq_zero_of_lt_vz (iotaInf_ne_zero ha) (m := -m) (by omega)
    rwa [iotaInf_coeff, neg_neg] at this

/-- **Finitely many Laurent polynomials have bounded valuation at both places.** -/
theorem finite_of_bounded_places (N : ℤ) :
    {a : BinaryLaurent | a ≠ 0 → -N ≤ ValuedMatrixTwo.vz zVal (iotaZero a) ∧
      -N ≤ ValuedMatrixTwo.vz zVal (iotaInf a)}.Finite := by
  classical
  let f : BinaryLaurent → (Finset.Icc (-N) N → ZMod 2) := fun a m ↦ a.coeff m
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro a ha b hb hab
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun m ↦ ?_)
  by_cases hm : m ∈ Finset.Icc (-N) N
  · exact congrFun hab ⟨m, hm⟩
  · have hm' : m < -N ∨ N < m := by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hm
      exact hm
    have hza : a.coeff m = 0 := by
      by_cases ha0 : a = 0
      · rw [ha0]; rfl
      · exact coeff_eq_zero_of_bounded_places ha0 (ha ha0).1 (ha ha0).2 hm'
    have hzb : b.coeff m = 0 := by
      by_cases hb0 : b = 0
      · rw [hb0]; rfl
      · exact coeff_eq_zero_of_bounded_places hb0 (hb hb0).1 (hb hb0).2 hm'
    rw [hza, hzb]

end JacobsonLaurent
end GroupApproximation

#audit_axioms GroupApproximation.JacobsonLaurent.finite_of_bounded_places
