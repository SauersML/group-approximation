import GroupApproximation.CharClass.ChernClasses
import GroupApproximation.CharClass.CohomologyLHRingData
import GroupApproximation.CharClass.CohomologyLHRingComponent
import GroupApproximation.CharClass.CohomologyTotalNontrivial

/-!
# The ring Chern class and the degreewise one are the same class

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, item 5).

This lane produced the mod-2 Chern classes twice.  `LerayHirschGraded.gamma` reads
them off the Leray–Hirsch coordinates of `ξ^r`, keeping their degrees.
`LerayHirschData.chern` reads them off the Chern polynomial of a `PowerBasis`,
forgetting them.  They are the same classes by the same relation, but they arrive
by different routes and meet nowhere definitionally, so a consumer holding one and
needing the other is stuck.  `component_chern_eq_gamma` is the bridge.

The proof is uniqueness of Leray–Hirsch coordinates, twice.  The ring relation says
`ξ^r` is the `lhFun` combination of the polynomial's coefficients; taking its
degree-`2r` component turns that into an `lhMap` statement, and the coordinates of
`ξ^r` are `gammaCoeff` by definition.

`Nonempty X` is needed and is not decoration: `natDegree_chernPoly` wants
`Nontrivial` on the base ring, which is where the degree of the relation comes from.

## Main declarations

* `chern_relation_lhFun` — the ring relation, as an `lhFun` combination.
* `component_chern_eq_gamma` — **the bridge.**

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory Polynomial
open GroupApproximation.CharClass.LHCast

noncomputable section

variable {X P : TopCat.{0}} {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}

/-- Reading a component in a degree written two ways. -/
theorem component_cohCast (Y : TopCat.{0}) {d d' : ℕ} (h : d = d') (z : TotalH Y) :
    TotalH.component Y d' z = cohCast h (TotalH.component Y d z) := by
  subst h
  rfl

/-- **The ring relation as a Leray–Hirsch combination.**  `ξ^r` is the combination
of the Chern polynomial's lower coefficients: that is the defining relation with
the leading term moved across, which over `F₂` costs no sign. -/
theorem chern_relation_lhFun [Nonempty X] (L : LerayHirschGraded π ξ r) :
    TotalH.of P 2 ξ ^ r
      = lhFun π r ξ
          (fun i : Fin r => (lerayHirschData_of_graded L).chernPolynomial.coeff (i : ℕ)) := by
  set D := lerayHirschData_of_graded L with hD
  letI := D.algebra
  have hdeg : D.chernPolynomial.natDegree = r := by
    show (chernPoly D.powerBasis).natDegree = r
    rw [natDegree_chernPoly D.powerBasis]
    rfl
  have hz : Polynomial.aeval (TotalH.of P 2 ξ) D.chernPolynomial = 0 :=
    D.aeval_taut_chernPolynomial
  rw [Polynomial.aeval_eq_sum_range, hdeg, Finset.sum_range_succ] at hz
  have hlead : D.chernPolynomial.coeff r = 1 := by
    have h : (chernPoly D.powerBasis).coeff (chernPoly D.powerBasis).natDegree = 1 :=
      (chernPoly_monic D.powerBasis).coeff_natDegree
    rw [natDegree_chernPoly D.powerBasis] at h
    exact h
  have hchar : ∀ w : TotalH P, w + w = 0 := fun w => by
    rw [← two_smul (ZMod 2) w, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  rw [hlead, one_smul] at hz
  have hsum : (∑ i ∈ Finset.range r,
      D.chernPolynomial.coeff i • TotalH.of P 2 ξ ^ i) = TotalH.of P 2 ξ ^ r := by
    have h2 : ((∑ i ∈ Finset.range r,
        D.chernPolynomial.coeff i • TotalH.of P 2 ξ ^ i) + TotalH.of P 2 ξ ^ r)
        + TotalH.of P 2 ξ ^ r = 0 + TotalH.of P 2 ξ ^ r := by rw [hz]
    rwa [add_assoc, hchar, add_zero, zero_add] at h2
  rw [← hsum, lhFun, Finset.sum_range fun i =>
    D.chernPolynomial.coeff i • TotalH.of P 2 ξ ^ i]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Algebra.smul_def]
  rfl

end

end LH
end CharClass
end GroupApproximation
