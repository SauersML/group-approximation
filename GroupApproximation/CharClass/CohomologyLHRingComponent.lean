import GroupApproximation.CharClass.CohomologyLHRingTerm
import GroupApproximation.CharClass.CohomologyLHRestrict

/-!
# `lhFun` in a degree is `lhMap`

The core of the bridge: the degree-`n` component of the ring-level Leray–Hirsch
combination is the degreewise combination applied to the componentwise coefficients.

Once this is in place, injectivity and surjectivity of `lhFun` are statements about
`lhMap` in each degree, which is what `LerayHirschGraded` gives.

Two things make it come out with no side condition.  The truncation `lhDomainCard`
encodes and the branch inside `lhTerm` are the same condition, so passing between
the ring-level range of summation and the degreewise one loses only terms that are
already zero.  And the contributing indices form an initial segment, so the
degreewise index type is a `Fin` rather than a subtype.

## Main declarations

* `LHCast.component_lhFun_term'` — one term, with the degree carried as an equation
  so that it can be substituted rather than rewritten under a dependent type.
* `LHCast.component_lhFun_term_gen` — one term at any degree, both cases.
* `LHCast.degFun` — the componentwise coefficients, as a total function.
* `LHCast.component_lhFun` — **the core lemma**.
-/

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

namespace LHCast

open LH

variable {X P : TopCat.{0}}

/-! ## 1. One term, at any degree -/

/-- One term, with its degree carried as an equation.  Stated this way so the
degree can be substituted; rewriting it in place fails, because the equation lives
in a type that depends on it. -/
theorem component_lhFun_term' (π : P ⟶ X) (ξ : Hmod2 P 2) (i m n : ℕ)
    (hn : 2 * i + m = n) (z : TotalH X) :
    TotalH.component P n (TotalH.map π z * TotalH.of P 2 ξ ^ i)
      = cohCast hn (cup (cupPowE ξ i) (pull π m (TotalH.component X m z))) := by
  subst hn
  rw [component_lhFun_term, cohCast_self]

/-- **One term of `lhFun` at any degree.**  Above `2i` it is the column term; below,
both sides vanish, and they vanish for the same reason on each side. -/
theorem component_lhFun_term_gen (π : P ⟶ X) (ξ : Hmod2 P 2) (n i : ℕ) (z : TotalH X) :
    TotalH.component P n (TotalH.map π z * TotalH.of P 2 ξ ^ i)
      = lhTerm π ξ n i (TotalH.component X (n - 2 * i) z) := by
  by_cases hi : 2 * i ≤ n
  · rw [component_lhFun_term' π ξ i (n - 2 * i) n (Nat.add_sub_cancel' hi) z,
      lhTerm_of_le π ξ hi, cup_comm, cohCast_cohCast]
  · rw [lhTerm_of_gt π ξ hi, component_lhFun_term_lt π ξ i n (by omega) z]

/-! ## 2. The componentwise coefficients -/

/-- The componentwise coefficients of a tuple of ring elements, as a **total**
function of the index, so that the two ranges of summation can be compared. -/
def degFun (X : TopCat.{0}) (r n : ℕ) (c : Fin r → TotalH X) :
    (i : ℕ) → Hmod2 X (n - 2 * i) :=
  fun i => if h : i < r then TotalH.component X (n - 2 * i) (c ⟨i, h⟩) else 0

/-! ## 3. The core lemma -/

set_option maxHeartbeats 1000000 in
/-- **The degree-`n` component of `lhFun` is `lhMap` on the componentwise
coefficients.** -/
theorem component_lhFun (π : P ⟶ X) (ξ : Hmod2 P 2) (r n : ℕ) (c : Fin r → TotalH X) :
    TotalH.component P n (lhFun π r ξ c)
      = lhMap π ξ r n (fun i => degFun X r n c (i : ℕ)) := by
  have hR : lhMap π ξ r n (fun i => degFun X r n c (i : ℕ))
      = ∑ i : Fin r, lhTerm π ξ n (i : ℕ) (degFun X r n c (i : ℕ)) := by
    rw [lhMap_eq_sum_lhTerm2 π ξ r n (lhDomainCard r n) rfl]
    exact (sum_lhTerm_truncate π ξ r n (degFun X r n c)).symm
  rw [hR]
  show TotalH.component P n
    (∑ i : Fin r, TotalH.map π (c i) * TotalH.of P 2 ξ ^ (i : ℕ)) = _
  rw [map_sum (TotalH.component P n)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [component_lhFun_term_gen]
  congr 1
  rw [degFun, dif_pos i.isLt]

end LHCast

end

end GroupApproximation.CharClass
