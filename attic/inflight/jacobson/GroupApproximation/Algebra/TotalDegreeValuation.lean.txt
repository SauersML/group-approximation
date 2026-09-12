import GroupApproximation.Algebra.ValuationWithTopInt
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Finiteness.Cardinality
import GroupApproximation.Meta.AxiomGuard

/-!
# The total-degree valuation of a rational function field

A step toward "every countable subgroup of `GL_2` over a field has the Haagerup property"
(`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring`, tex lines 1146--1147).
A finitely generated field of characteristic `p` is finite over a rational function field
`k(t_1, …, t_d)` with `k` finite (Noether normalization), and the place of that field "at infinity"
is the total degree: `v (f / g) = deg g − deg f`.

* `degValuation k d : Valuation (FractionRing (MvPolynomial (Fin d) k)) ℤᵐ⁰` is the extension to
  the fraction field of `p ↦ exp (totalDegree p)`;
* `degVal k d`, its additive form, has the uniformizer `(t_i)⁻¹` (`degVal_inv_X`);
* a nonzero polynomial has `-N ≤ degVal p` exactly when its total degree is at most `N`
  (`neg_le_degVal_algebraMap_iff`);
* over a finite field, polynomials of bounded total degree form a finite set
  (`finite_setOf_totalDegree_le`).
-/

namespace GroupApproximation
namespace TotalDegreeValuation

open WithZero

variable (k : Type*) [Field k] (d : ℕ)

open Classical in
/-- `p ↦ exp (totalDegree p)`, with value `0` at `0`. -/
noncomputable def degFun (p : MvPolynomial (Fin d) k) : ℤᵐ⁰ :=
  if p = 0 then 0 else exp (p.totalDegree : ℤ)

variable {k d}

theorem degFun_zero : degFun k d 0 = 0 := by
  rw [degFun, if_pos rfl]

theorem degFun_of_ne_zero {p : MvPolynomial (Fin d) k} (hp : p ≠ 0) :
    degFun k d p = exp (p.totalDegree : ℤ) := by
  rw [degFun, if_neg hp]

theorem degFun_one : degFun k d 1 = 1 := by
  rw [degFun_of_ne_zero one_ne_zero, MvPolynomial.totalDegree_one, Nat.cast_zero, exp_zero]

theorem degFun_mul (p q : MvPolynomial (Fin d) k) :
    degFun k d (p * q) = degFun k d p * degFun k d q := by
  by_cases hp : p = 0
  · rw [hp, zero_mul, degFun_zero, zero_mul]
  by_cases hq : q = 0
  · rw [hq, mul_zero, degFun_zero, mul_zero]
  rw [degFun_of_ne_zero (mul_ne_zero hp hq), degFun_of_ne_zero hp, degFun_of_ne_zero hq,
    MvPolynomial.totalDegree_mul_of_isDomain hp hq, Nat.cast_add, exp_add]

theorem degFun_add (p q : MvPolynomial (Fin d) k) :
    degFun k d (p + q) ≤ max (degFun k d p) (degFun k d q) := by
  by_cases hpq : p + q = 0
  · rw [hpq, degFun_zero]
    simp
  by_cases hp : p = 0
  · rw [hp, zero_add]
    exact le_max_right _ _
  by_cases hq : q = 0
  · rw [hq, add_zero]
    exact le_max_left _ _
  rw [degFun_of_ne_zero hpq, degFun_of_ne_zero hp, degFun_of_ne_zero hq]
  rcases le_max_iff.mp (MvPolynomial.totalDegree_add p q) with h | h
  · exact le_max_iff.mpr (Or.inl (exp_le_exp.mpr (by exact_mod_cast h)))
  · exact le_max_iff.mpr (Or.inr (exp_le_exp.mpr (by exact_mod_cast h)))

variable (k d)

/-- The total-degree valuation on polynomials. -/
noncomputable def degValuationPoly : Valuation (MvPolynomial (Fin d) k) ℤᵐ⁰ where
  toFun := degFun k d
  map_zero' := degFun_zero
  map_one' := degFun_one
  map_mul' := degFun_mul
  map_add_le_max' := degFun_add

theorem degValuationPoly_apply (p : MvPolynomial (Fin d) k) :
    degValuationPoly k d p = degFun k d p :=
  rfl

theorem nonZeroDivisors_le_primeCompl :
    nonZeroDivisors (MvPolynomial (Fin d) k) ≤ (degValuationPoly k d).supp.primeCompl := by
  intro p hp
  rw [Ideal.mem_primeCompl_iff, Valuation.mem_supp_iff, degValuationPoly_apply,
    degFun_of_ne_zero (nonZeroDivisors.ne_zero hp)]
  exact exp_ne_zero

/-- **The total-degree valuation** on `k(t_1, …, t_d)`. -/
noncomputable def degValuation : Valuation (FractionRing (MvPolynomial (Fin d) k)) ℤᵐ⁰ :=
  (degValuationPoly k d).extendToLocalization (nonZeroDivisors_le_primeCompl k d)
    (FractionRing (MvPolynomial (Fin d) k))

theorem degValuation_algebraMap (p : MvPolynomial (Fin d) k) :
    degValuation k d (algebraMap _ (FractionRing (MvPolynomial (Fin d) k)) p) = degFun k d p :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ p

/-- The additive total-degree valuation. -/
noncomputable def degVal : AddValuation (FractionRing (MvPolynomial (Fin d) k)) (WithTop ℤ) :=
  ValuationWithTopInt.addVal (degValuation k d)

theorem algebraMap_ne_zero {p : MvPolynomial (Fin d) k} (hp : p ≠ 0) :
    algebraMap _ (FractionRing (MvPolynomial (Fin d) k)) p ≠ 0 := fun h ↦
  hp (IsFractionRing.to_map_eq_zero_iff.mp h)

/-- **Uniformizers.**  `(t_i)⁻¹` has total-degree valuation `1`. -/
theorem degVal_inv_X (i : Fin d) :
    degVal k d (algebraMap (MvPolynomial (Fin d) k) (FractionRing (MvPolynomial (Fin d) k))
      (MvPolynomial.X i))⁻¹ = 1 := by
  refine ValuationWithTopInt.addVal_eq_one _ ?_
  rw [map_inv₀, degValuation_algebraMap, degFun_of_ne_zero (MvPolynomial.X_ne_zero i),
    MvPolynomial.totalDegree_X, Nat.cast_one, exp_neg]

/-- **Bounded valuation is bounded total degree.** -/
theorem neg_le_degVal_algebraMap_iff {p : MvPolynomial (Fin d) k} (hp : p ≠ 0) (N : ℕ) :
    (((-(N : ℤ)) : ℤ) : WithTop ℤ) ≤ degVal k d (algebraMap _ (FractionRing (MvPolynomial (Fin d) k)) p) ↔
      p.totalDegree ≤ N := by
  rw [degVal, ValuationWithTopInt.neg_le_addVal_iff _ (algebraMap_ne_zero k d hp),
    degValuation_algebraMap, degFun_of_ne_zero hp, exp_le_exp]
  exact Nat.cast_le

/-- **Over a finite field, polynomials of bounded total degree form a finite set.** -/
theorem finite_setOf_totalDegree_le [Finite k] (N : ℕ) :
    {p : MvPolynomial (Fin d) k | p.totalDegree ≤ N}.Finite := by
  haveI : Finite (MvPolynomial.restrictTotalDegree (Fin d) k N) := Module.finite_of_finite k
  refine (Set.finite_range
    (fun x : MvPolynomial.restrictTotalDegree (Fin d) k N ↦ (x : MvPolynomial (Fin d) k))).subset ?_
  intro p hp
  exact ⟨⟨p, (MvPolynomial.mem_restrictTotalDegree (Fin d) N p).mpr hp⟩, rfl⟩

end TotalDegreeValuation
end GroupApproximation

#audit_axioms GroupApproximation.TotalDegreeValuation.degVal_inv_X
#audit_axioms GroupApproximation.TotalDegreeValuation.neg_le_degVal_algebraMap_iff
#audit_axioms GroupApproximation.TotalDegreeValuation.finite_setOf_totalDegree_le
