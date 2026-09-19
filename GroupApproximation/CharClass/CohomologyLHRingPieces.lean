import GroupApproximation.CharClass.CohomologyLHDegreewise
import GroupApproximation.CharClass.SqDataInstance
import GroupApproximation.CharClass.ChernClasses

/-!
# Two pieces of the bridge from degreewise to ring-level Leray–Hirsch

`LerayHirschData.free` is bijectivity of `lhFun`, a statement about the whole ring;
`LerayHirschGraded` is bijectivity of `lhMap` in each degree.  The bridge between
them is degree bookkeeping, and these are the two pieces of it that are pure
algebra, with no direct-sum support argument in either.

`totalH_of_pow` identifies the `i`-th power of the degree-two generator, taken in
the ring, with the cup power concentrated in degree `2i`.  `sum_lhTerm_truncate`
says the ring-level sum over all `r` indices and the degreewise sum over
`lhDomainCard r n` of them agree, because the discarded terms are exactly those
whose power has outrun the degree, where `lhTerm` is already zero by definition.

That second one is why no side condition appears anywhere downstream: the
truncation `lhDomainCard` encodes and the `if` inside `lhTerm` are the same
condition, so the two sums differ by terms that are zero rather than by terms that
have to be shown small.

## Main declarations

* `LHCast.totalH_of_pow` — the power of the generator, concentrated.
* `LHCast.lhDomainCard_le` — the cardinal is at most the rank.
* `LHCast.sum_lhTerm_truncate` — the two ranges of summation agree.
-/

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

namespace LHCast

open LH

variable {X P : TopCat.{0}}

/-! ## 1. Powers of the generator -/

/-- **The `i`-th power of the degree-two generator is the cup power**, concentrated
in degree `2i`.  Proved by induction, with the successor degree written as
`2 * j + 2` so that `TotalH.of_mul` can see the summand boundary. -/
theorem totalH_of_pow (ξ : Hmod2 P 2) :
    ∀ i : ℕ, TotalH.of P 2 ξ ^ i = TotalH.of P (2 * i) (cupPowE ξ i) := by
  intro i
  induction i with
  | zero => rw [pow_zero, cupPowE_zero, TotalH.of_one]
  | succ j ih =>
    show TotalH.of P 2 ξ ^ (j + 1) = TotalH.of P (2 * j + 2) (cupPowE ξ (j + 1))
    rw [pow_succ, ih, cupPowE_succ, TotalH.of_mul]

/-! ## 2. The two ranges of summation -/

theorem lhDomainCard_le (r n : ℕ) : lhDomainCard r n ≤ r := by
  unfold lhDomainCard
  omega

/-- **The ring-level range and the degreewise range agree.**  The terms the
degreewise sum omits are those with `2i > n`, where `lhTerm` is zero by its own
definition, so nothing is lost. -/
theorem sum_lhTerm_truncate (π : P ⟶ X) (ξ : Hmod2 P 2) (r n : ℕ)
    (f : (i : ℕ) → Hmod2 X (n - 2 * i)) :
    ∑ i : Fin r, lhTerm π ξ n (i : ℕ) (f (i : ℕ))
      = ∑ i : Fin (lhDomainCard r n), lhTerm π ξ n (i : ℕ) (f (i : ℕ)) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => lhTerm π ξ n i (f i)) r,
    Fin.sum_univ_eq_sum_range (fun i => lhTerm π ξ n i (f i)) (lhDomainCard r n)]
  refine (Finset.sum_subset (fun x hx => ?_) ?_).symm
  · simp only [Finset.mem_range] at hx ⊢
    exact lt_of_lt_of_le hx (lhDomainCard_le r n)
  intro i hi hni
  simp only [Finset.mem_range] at hi hni
  refine lhTerm_of_gt π ξ ?_ (f i)
  unfold lhDomainCard at hni
  omega

end LHCast

end

end GroupApproximation.CharClass
