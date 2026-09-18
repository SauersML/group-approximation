import Mathlib.RingTheory.NoetherNormalization
import GroupApproximation.Meta.AxiomGuard

/-!
# Nagata's change of variables over an integral domain: degrees

Lane `bh-met-91n`, part 1.  The lemmas below are the proof by Nagata in Mathlib's
`Mathlib/RingTheory/NoetherNormalization.lean` (Copyright (c) 2025 Sihan Su; Apache 2.0;
authors Riccardo Brasca, Sihan Su, Wan Lin, Xiaoyang Su), where they are `private` and stated
over a field.  Here the base is only an integral domain `R` (every step of the degree
computation needs only `NoZeroDivisors` and `Nontrivial`); names carry the prefix
`suslinMonic_` and `private` is dropped.  The automorphism `suslinMonic_T f` of
`R[X_0,…,X_n]` maps `X_i` to `X_i + X_0 ^ (up ^ i)` for `i ≠ 0`, `up = 2 + totalDegree f`,
and sends distinct monomials of `f` to polynomials of distinct `X_0`-degree.
-/

open Polynomial MvPolynomial Ideal Nat RingHom List

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) R)
variable (v w : Fin (n + 1) →₀ ℕ)

section equivT

-- Mathlib's lakefile builds the original proofs with this option (core default: 1).
set_option maxSynthPendingDepth 3

/-- `up` is defined as `2 + f.totalDegree`. Any big enough number would work. -/
local notation3 "up" => 2 + f.totalDegree

omit [IsDomain R] in
variable {f v} in
theorem suslinMonic_lt_up (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  grind

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_lt_up

/-- `r` maps `(i : Fin (n + 1))` to `up ^ i`. -/
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

/-- The algebra map `suslinMonic_T1 f c` maps `X_i` into `X_i + c • X_0 ^ r_i` when `i ≠ 0`
and `X_0` to `X_0`. -/
noncomputable abbrev suslinMonic_T1 (c : R) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ r i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_T1

omit [IsDomain R] in
theorem suslinMonic_t1_comp_t1_neg (c : R) :
    (suslinMonic_T1 f c).comp (suslinMonic_T1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_t1_comp_t1_neg

/-- `suslinMonic_T1 f 1` leads to an algebra equiv `suslinMonic_T f`. -/
noncomputable abbrev suslinMonic_T :=
  AlgEquiv.ofAlgHom (suslinMonic_T1 f 1) (suslinMonic_T1 f (-1))
    (suslinMonic_t1_comp_t1_neg f 1) (by simpa using suslinMonic_t1_comp_t1_neg f (-1))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_T

omit [IsDomain R] in
theorem suslinMonic_sum_r_mul_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine ne <| Finsupp.ext <| congrFun <| ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (suslinMonic_lt_up vlt) (suslinMonic_lt_up wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
    Fin.val_cast, mul_comm, sum_ofFn] using! h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_sum_r_mul_ne

theorem suslinMonic_degreeOf_zero_t {a : R} (ha : a ≠ 0) :
    ((suslinMonic_T f) (monomial v a)).degreeOf 0 = ∑ i : Fin (n + 1), (r i) * v i := by
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero,
    ite_false, one_smul, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ, algebraMap_eq]
  have h (i : Fin n) :
      (Polynomial.C (X (R := R) i) + Polynomial.X ^ r i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp <| by simp [add_comm, leadingCoeff_X_pow_add_C])
  rw [natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ h i))), natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    natDegree_prod _ _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero, pow_zero, one_mul,
    add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), natDegree_X_pow_add_C, mul_comm])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_degreeOf_zero_t

/-- `suslinMonic_T` maps different monomials of `f` to polynomials with different degrees in
`X_0`. -/
theorem suslinMonic_degreeOf_t_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support)
    (ne : v ≠ w) :
    (suslinMonic_T f <| monomial v <| coeff v f).degreeOf 0 ≠
    (suslinMonic_T f <| monomial w <| coeff w f).degreeOf 0 := by
  rw [suslinMonic_degreeOf_zero_t _ _ <| mem_support_iff.mp hv,
    suslinMonic_degreeOf_zero_t _ _ <| mem_support_iff.mp hw]
  refine suslinMonic_sum_r_mul_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_degreeOf_t_ne_of_ne

end equivT

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
