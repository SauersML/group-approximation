import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittECoeff
import Mathlib.RingTheory.WittVector.Truncated
import Mathlib.RingTheory.WittVector.Compare
import GroupApproximation.Meta.AxiomGuard

/-!
# Truncated Witt vectors of length `e` (bh-met-87h, part 6)

Facts about `TruncatedWittVector p e R`.

* Coordinates of sums and products can be computed on the lifts `out`
  (`eHighWittE_tw_add_coeff`, `eHighWittE_tw_mul_coeff`).
* In characteristic `p`, we have `p ^ e = 0` (`eHighWittE_tw_p_pow_eq_zero`).
* Also `p ^ j ≠ 0` for `j < e` (`eHighWittE_tw_p_pow_ne_zero`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

noncomputable section

variable {p : ℕ} {R : Type*} [Fact p.Prime] [CommRing R] {e : ℕ}

theorem eHighWittE_truncate_out (x : TruncatedWittVector p e R) :
    WittVector.truncate e x.out = x :=
  TruncatedWittVector.ext fun i => by
    rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_out]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_truncate_out

theorem eHighWittE_tw_add_coeff (x y : TruncatedWittVector p e R) (i : Fin e) :
    (x + y).coeff i = (x.out + y.out).coeff (i : ℕ) := by
  rw [← WittVector.coeff_truncate, map_add, eHighWittE_truncate_out, eHighWittE_truncate_out]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_tw_add_coeff

theorem eHighWittE_tw_mul_coeff (x y : TruncatedWittVector p e R) (i : Fin e) :
    (x * y).coeff i = (x.out * y.out).coeff (i : ℕ) := by
  rw [← WittVector.coeff_truncate, map_mul, eHighWittE_truncate_out, eHighWittE_truncate_out]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_tw_mul_coeff

/-- `p ^ e = 0` in `TruncatedWittVector p e R` when `R` has characteristic `p`. -/
theorem eHighWittE_tw_p_pow_eq_zero [CharP R p] :
    (p : TruncatedWittVector p e R) ^ e = 0 := by
  have h : (p : TruncatedWittVector p e R) ^ e =
      WittVector.truncate e ((p : WittVector p R) ^ e) := by
    rw [map_pow, map_natCast]
  rw [h]
  refine TruncatedWittVector.ext fun i => ?_
  rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero,
    WittVector.coeff_p_pow_eq_zero p R (Nat.ne_of_lt i.isLt)]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_tw_p_pow_eq_zero

/-- `p ^ j ≠ 0` in `TruncatedWittVector p e R` for `j < e`. -/
theorem eHighWittE_tw_p_pow_ne_zero [CharP R p] {j : ℕ} (hj : j < e) :
    (p : TruncatedWittVector p e R) ^ j ≠ 0 := fun h =>
  Nat.ne_of_lt hj (TruncatedWittVector.eq_of_le_of_cast_pow_eq_zero p e R j hj.le h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_tw_p_pow_ne_zero

end

end GroupApproximation.BooneHigman.Metabelian.Coprimary
