import GroupApproximation.AlgTop.ChernSeries
import GroupApproximation.AlgTop.ChernNewtonSquareZero
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-!
# Vieta and Newton for a split total Chern class

The splitting principle says that a Chern-class computation may be carried out as
if the bundle were a sum of line bundles.  This file supplies the *algebra* on
the far side of that principle: for a total Chern class that is literally a
product of line classes,

```text
c = ∏_i (1 + a_i X),
```

the `k`-th Chern class is the `k`-th elementary symmetric function of the Chern
roots `a_i` (`chernClass_prod_line`, Vieta), and the Chern classes together with
the power sums `p_q = ∑_i a_i^q` satisfy **Newton's identity**
(`newton_of_split`), obtained by evaluating Mathlib's
`MvPolynomial.mul_esymm_eq_sum` at the roots.

The point of `newton_of_split` is that it *discharges* the `hnewton` hypothesis
of `GroupApproximation.AlgTop.natCast_mul_chern_eq_of_squareZero`.  The
combination `chern_eq_of_squareZero_of_split` below is therefore a statement
about split classes with no unproved algebraic input at all: only the square-zero
hypothesis on the ambient ring, which is what `z² = 0` supplies in the
manuscript.

## Main declarations

* `TotalChern.prod_series` — `series` is multiplicative over finite products.
* `TotalChern.chernClass_prod_line` — Vieta.
* `TotalChern.newton_of_split` — Newton's identity for a split class.
* `TotalChern.natCast_mul_chernClass_of_split_squareZero` — the square-zero
  Newton step with its Newton hypothesis discharged.
-/

namespace GroupApproximation
namespace AlgTop
namespace TotalChern

open Finset (antidiagonal mem_antidiagonal)
open scoped PowerSeries

noncomputable section

variable {A : Type*} [CommRing A]

theorem prod_series {ι : Type*} (s : Finset ι) (c : ι → TotalChern A) :
    (∏ i ∈ s, c i).series = ∏ i ∈ s, (c i).series := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_series, ih]

/-- **Vieta.**  The `k`-th Chern class of a split total Chern class is the `k`-th
elementary symmetric function of its Chern roots. -/
theorem chernClass_prod_line {ι : Type*} (s : Finset ι) (a : ι → A) (k : ℕ) :
    (∏ i ∈ s, line (a i)).chernClass k = ∑ t ∈ s.powersetCard k, ∏ i ∈ t, a i := by
  classical
  have h1 : (∏ i ∈ s, line (a i)).series
      = ∑ t ∈ s.powerset, PowerSeries.C (∏ i ∈ t, a i) * PowerSeries.X ^ t.card := by
    rw [prod_series]
    have hline : ∀ i : ι,
        (line (a i)).series = PowerSeries.C (a i) * PowerSeries.X + 1 := by
      intro i
      rw [line_series, add_comm]
    simp only [hline]
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const,
      ← map_prod]
  rw [chernClass, h1, map_sum, Finset.powersetCard_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [PowerSeries.coeff_C_mul_X_pow]
  by_cases h : t.card = k
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun hh => h hh.symm), if_neg h]

/-- **Newton's identity for a split total Chern class.**  This is Mathlib's
`MvPolynomial.mul_esymm_eq_sum` evaluated at the Chern roots. -/
theorem newton_of_split {ι : Type*} [Fintype ι] (a : ι → A) (k : ℕ) :
    (k : A) * (∏ i, line (a i)).chernClass k
      = (-1) ^ (k + 1) *
        ∑ q ∈ Finset.filter (fun q : ℕ × ℕ => q.1 < k) (antidiagonal k),
          (-1) ^ q.1 * (∏ i, line (a i)).chernClass q.1 * (∑ i, a i ^ q.2) := by
  classical
  have hes : ∀ m : ℕ, MvPolynomial.aeval a (MvPolynomial.esymm ι A m)
      = (∏ i, line (a i)).chernClass m := by
    intro m
    rw [MvPolynomial.esymm, map_sum, chernClass_prod_line]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => MvPolynomial.aeval_X a i
  have hps : ∀ m : ℕ, MvPolynomial.aeval a (MvPolynomial.psum ι A m) = ∑ i, a i ^ m := by
    intro m
    rw [MvPolynomial.psum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_pow, MvPolynomial.aeval_X]
  have hmain := congrArg (MvPolynomial.aeval a) (MvPolynomial.mul_esymm_eq_sum ι A k)
  simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast, hes, hps] at hmain
  exact hmain

/-- The square-zero Newton step for a **split** total Chern class, with the
Newton hypothesis discharged.  Only the square-zero hypothesis remains, and in
the manuscript that is exactly `z² = 0`. -/
theorem natCast_mul_chernClass_of_split_squareZero {ι : Type*} [Fintype ι] (a : ι → A)
    (hsq : ∀ i j : ℕ, 0 < i → 0 < j →
      (∏ x, line (a x)).chernClass i * (∑ x, a x ^ j) = 0)
    {k : ℕ} (hk : 0 < k) :
    (k : A) * (∏ i, line (a i)).chernClass k = (-1) ^ (k + 1) * ∑ i, a i ^ k :=
  natCast_mul_chern_eq_of_squareZero (fun m => (∏ i, line (a i)).chernClass m)
    (fun m => ∑ i, a i ^ m) (chernClass_zero _) (newton_of_split a) hsq hk

end

end TotalChern
end AlgTop
end GroupApproximation
