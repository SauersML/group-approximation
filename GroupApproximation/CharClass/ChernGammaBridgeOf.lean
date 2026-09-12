import GroupApproximation.CharClass.ChernClassesOf
import GroupApproximation.CharClass.ChernClassesEvenOf

/-!
# The Chern relation as a Leray–Hirsch combination, over `K`

The coefficient-generic form of `ChernGammaBridge.chern_relation_lhFun`, for the whole-ring
carrier `LerayHirschDataOf` and for the even-part carrier `LerayHirschDataEvenOf`.

**The sign.**  The defining relation is the monic `ξ^r + γ_1 ξ^{r-1} + ⋯ + γ_r = 0`, so moving the
leading term across gives

```text
ξ^r = ∑_{i<r} (−coeff_i) · ξ^i,
```

and the Leray–Hirsch coordinates of `ξ^r` are the **negatives** of the lower coefficients of the
Chern polynomial.  Over `F₂` the minus is invisible, which is why `chern_relation_lhFun` has none.
Consequently the degreewise class `LerayHirschGraded.gamma k`, which *is* a Leray–Hirsch coordinate
of `ξ^r`, is `−γ_k` over `K` for `1 ≤ k ≤ r`; a consumer at an odd prime must not read `gamma` as
the Chern class.  The ring Chern classes `chern k` follow `ChernRelation`'s convention.

## Main declarations

* `LerayHirschDataOf.chern_relation_lhFunOf`.
* `LerayHirschDataEvenOf.chern_relation_lhFunEvenOf`.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory Polynomial

noncomputable section

variable {X P : TopCat.{0}} {K : Type} [CommRing K]

/-- **The ring relation as a Leray–Hirsch combination, over `K`**, on the even parts: `ξ^r` is
the combination of the negated lower coefficients of the Chern polynomial. -/
theorem LerayHirschDataEvenOf.chern_relation_lhFunEvenOf (D : LerayHirschDataEvenOf K X P)
    [Nontrivial (Gen.evenPart K X)] :
    evenTautOf K D.taut ^ D.rank
      = lhFunEvenOf K D.proj D.rank D.taut
          (fun i : Fin D.rank => -D.chernPolynomial.coeff (i : ℕ)) := by
  letI := D.algebra
  have hdeg : D.chernPolynomial.natDegree = D.rank := by
    show (chernPoly D.powerBasis).natDegree = D.rank
    rw [natDegree_chernPoly D.powerBasis]
    rfl
  have hz : Polynomial.aeval (evenTautOf K D.taut) D.chernPolynomial = 0 :=
    D.aeval_taut_chernPolynomial
  rw [Polynomial.aeval_eq_sum_range, hdeg, Finset.sum_range_succ] at hz
  have hlead : D.chernPolynomial.coeff D.rank = 1 := by
    have h : (chernPoly D.powerBasis).coeff (chernPoly D.powerBasis).natDegree = 1 :=
      (chernPoly_monic D.powerBasis).coeff_natDegree
    rw [natDegree_chernPoly D.powerBasis] at h
    exact h
  rw [hlead, one_smul] at hz
  rw [eq_neg_of_add_eq_zero_right hz, ← Finset.sum_neg_distrib, lhFunEvenOf,
    Finset.sum_range fun i => -(D.chernPolynomial.coeff i • evenTautOf K D.taut ^ i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Algebra.smul_def, map_neg, neg_mul]
  rfl

/-- **The ring relation as a Leray–Hirsch combination, over `K`**, for the whole-ring carrier. -/
theorem LerayHirschDataOf.chern_relation_lhFunOf (D : LerayHirschDataOf K X P)
    [Nontrivial (TotalHOf K X)] :
    TotalHOf.of K P 2 D.taut ^ D.rank
      = lhFunOf K D.proj D.rank D.taut
          (fun i : Fin D.rank => -D.chernPolynomial.coeff (i : ℕ)) := by
  letI := D.commRing
  letI := D.algebra
  have hdeg : D.chernPolynomial.natDegree = D.rank := by
    show (chernPoly D.powerBasis).natDegree = D.rank
    rw [natDegree_chernPoly D.powerBasis]
    rfl
  have hz : Polynomial.aeval (TotalHOf.of K P 2 D.taut) D.chernPolynomial = 0 :=
    D.aeval_taut_chernPolynomial
  rw [Polynomial.aeval_eq_sum_range, hdeg, Finset.sum_range_succ] at hz
  have hlead : D.chernPolynomial.coeff D.rank = 1 := by
    have h : (chernPoly D.powerBasis).coeff (chernPoly D.powerBasis).natDegree = 1 :=
      (chernPoly_monic D.powerBasis).coeff_natDegree
    rw [natDegree_chernPoly D.powerBasis] at h
    exact h
  rw [hlead, one_smul] at hz
  rw [eq_neg_of_add_eq_zero_right hz, ← Finset.sum_neg_distrib, lhFunOf,
    Finset.sum_range fun i => -(D.chernPolynomial.coeff i • TotalHOf.of K P 2 D.taut ^ i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Algebra.smul_def, map_neg, neg_mul]
  rfl

end

end CharClass
end GroupApproximation
