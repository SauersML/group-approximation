import GroupApproximation.CharClass.CohomologyLHRingPieces

/-!
# The contributing indices, and one term of `lhFun` in a degree

Two more pieces of the bridge from degreewise to ring-level Leray–Hirsch.

`mem_lhDomain_iff` is the fact that makes `Fin (lhDomainCard r n)` the right index
type rather than a subtype of `Fin r`: the two conditions on a contributing index,
`i < r` and `2i ≤ n`, are both of the form "below something", so the indices that
contribute form an **initial segment** and their count is the minimum.  If that
failed the whole bookkeeping would need a subtype instead.  It is obvious once
stated and invisible otherwise, which is why it is stated.

`component_lhFun_term` computes one term of `lhFun` in a degree.  Its degree is
written `2 * i + m` rather than with a subtraction, so no cast appears: the term
lands in degree `2i` above the degree its coefficient is read in.

## Main declarations

* `LHCast.mem_lhDomain_iff` — the contributing indices are an initial segment.
* `LHCast.component_lhFun_term` — one term of `lhFun`, in a degree.
-/

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

namespace LHCast

open LH

variable {X P : TopCat.{0}}

/-- **The contributing indices form an initial segment.**  Both conditions on a
contributing index are of the form "below something", so their conjunction is
"below the minimum", which is what `lhDomainCard` is.  This is what makes
`Fin (lhDomainCard r n)` the correct index type rather than a subtype of
`Fin r`. -/
theorem mem_lhDomain_iff (r n i : ℕ) : i < lhDomainCard r n ↔ i < r ∧ 2 * i ≤ n := by
  unfold lhDomainCard
  omega

/-- **One term of `lhFun`, in a degree.**  The coefficient is read `2i` degrees
below, and the degree is written as a sum rather than with a subtraction so that
no cast enters.  `TotalH` is commutative through its graded structure, which is
what lets `cc-wu`'s `component_of_mul` apply with the concentrated factor moved to
the left. -/
theorem component_lhFun_term (π : P ⟶ X) (ξ : Hmod2 P 2) (i m : ℕ) (z : TotalH X) :
    TotalH.component P (2 * i + m) (TotalH.map π z * TotalH.of P 2 ξ ^ i)
      = cup (cupPowE ξ i) (pull π m (TotalH.component X m z)) := by
  have hpow : TotalH.map π z * TotalH.of P 2 ξ ^ i
      = TotalH.of P (2 * i) (cupPowE ξ i) * TotalH.map π z := by
    rw [totalH_of_pow, mul_comm]
  rw [hpow, Wu.component_of_mul, Wu.totalH_component_map]

/-- The same term in a degree it cannot reach: below `2i` there is nothing. -/
theorem component_lhFun_term_lt (π : P ⟶ X) (ξ : Hmod2 P 2) (i n : ℕ) (hn : n < 2 * i)
    (z : TotalH X) :
    TotalH.component P n (TotalH.map π z * TotalH.of P 2 ξ ^ i) = 0 := by
  rw [totalH_of_pow, mul_comm]
  induction z using DirectSum.induction_on with
  | zero => rw [map_zero, mul_zero, map_zero]
  | of k a =>
    show TotalH.component P n
      (TotalH.of P (2 * i) (cupPowE ξ i) * TotalH.map π (TotalH.of X k a)) = 0
    rw [TotalH.map_of, ← TotalH.of_mul]
    exact Wu.component_of_ne (by omega) _
  | add u v hu hv => rw [map_add, mul_add, map_add, hu, hv, add_zero]

end LHCast

end

end GroupApproximation.CharClass
