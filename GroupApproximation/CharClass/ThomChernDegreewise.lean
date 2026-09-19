import GroupApproximation.CharClass.CohomologyLHDegreewise
import GroupApproximation.CharClass.CohomologyAssoc

/-!
# The Chern relation, degreewise

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/ThomChernBasis.lean` solves the Chern relation for the top power of the
generator inside a `PowerBasis`, which is the **ring** view.  The degreewise Thom
algebra of `CharClass/ThomFreeDegreewise.lean` needs the same relation as an
equation between elements of `H^{2r}(P)`, and the ring view does not deliver that
without a transport through `TotalH`.

It turns out no transport is needed.  `LerayHirschGraded.gammaCoeff` already *is*
the degreewise relation: it is the coefficient family of `ξ^r`, and
`lhMap_gammaCoeff` says the combination of that family is `ξ^r`.  This file
reindexes it by `Fin r` and turns it into the statement the restriction square
consumes:

```text
lhTerm π ξ (2r) r a  =  ∑_{i < r} lhTerm π ξ (2r) i (γ_{r-i} ⌣ a).
```

The only work is the cup-product bookkeeping: cupping a column term with a
pulled-back class of the base is again a column term, at the same index and a
raised ambient degree.  That is `cup_pull_lhTerm`, and everything else is a sum
of instances of it.

## Main declarations

* `ThomChernDeg.cup_pull_lhTerm` — `π^*a ⌣ lhTerm π ξ n i b = lhTerm π ξ (p+n) i (a ⌣ b)`.
* `ThomChernDeg.chernCoeff` — the coefficients of `ξ^r`, reindexed by `Fin r`.
* `ThomChernDeg.chernMul` — multiplication by the `i`-th coefficient, as a linear map.
* `ThomChernDeg.lhTerm_top_eq_sum` — **the degreewise Chern relation**.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace ThomChernDeg

open LH

set_option linter.unusedSectionVars false

variable {X P : TopCat.{0}}

/-! ## 1. A degree transport across a finite sum -/

/-- `cohCast` commutes with a finite sum.  Stated here because the cohomology
layer has `cohCast_add` but no sum form. -/
theorem cohCast_sum {m m' : ℕ} (h : m = m') {ι : Type} [Fintype ι]
    (F : ι → Hmod2 X m) : cohCast h (∑ i, F i) = ∑ i, cohCast h (F i) := by
  subst h; rfl

/-! ## 2. Cupping a column term with a class of the base -/

/-- **A column term times a pulled-back class is a column term.**  The index is
unchanged and the ambient degree rises by the degree of the class; the coefficient
is the cup product of the two coefficients. -/
theorem cup_pull_lhTerm (π : P ⟶ X) (ξ : Hmod2 P 2) {p n i : ℕ} (hi : 2 * i ≤ n)
    (a : Hmod2 X p) (b : Hmod2 X (n - 2 * i)) :
    cup (pull π p a) (lhTerm π ξ n i b)
      = lhTerm π ξ (p + n) i
          (cohCast (by omega : p + (n - 2 * i) = p + n - 2 * i) (cup a b)) := by
  rw [lhTerm_of_le π ξ hi, lhTerm_of_le π ξ (show 2 * i ≤ p + n by omega),
    cup_cohCast_right, ← cup_assoc, ← pull_cup, cohCast_cohCast,
    pull_cohCast, cup_cohCast_left, cohCast_cohCast]

/-- The same with the ambient degree given by an equation, so that it can be used
at a degree that is not syntactically `p + n`. -/
theorem cup_pull_lhTerm' (π : P ⟶ X) (ξ : Hmod2 P 2) {p n m i : ℕ} (hi : 2 * i ≤ n)
    (hm : p + n = m) (a : Hmod2 X p) (b : Hmod2 X (n - 2 * i)) :
    cohCast hm (cup (pull π p a) (lhTerm π ξ n i b))
      = lhTerm π ξ m i (cohCast (by omega : p + (n - 2 * i) = m - 2 * i) (cup a b)) := by
  subst hm
  rw [cohCast_self]
  exact cup_pull_lhTerm π ξ hi a b

/-! ## 3. The Chern coefficients, reindexed -/

/-- The coefficients of `ξ^r` in the Leray–Hirsch presentation, reindexed by
`Fin r`.  In the classical notation `chernCoeff L i` is `γ_{r-i}`, sitting in
`H^{2r-2i}(X)`. -/
def chernCoeff {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ} (L : LerayHirschGraded π ξ r)
    (i : Fin r) : Hmod2 X (2 * r - 2 * (i : ℕ)) :=
  LHCast.lhDomainEquiv X r (2 * r) (lhDomainCard_two_mul r) L.gammaCoeff i

/-- **The defining relation, reindexed**: `ξ^r` is the combination of its own
coefficients. -/
theorem sum_lhTerm_chernCoeff {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) :
    ∑ i : Fin r, lhTerm π ξ (2 * r) (i : ℕ) (chernCoeff L i) = cupPowE ξ r := by
  rw [← L.lhMap_gammaCoeff]
  exact (LHCast.lhMap_eq_sum_lhTerm π ξ r (2 * r) (lhDomainCard_two_mul r)
    L.gammaCoeff).symm

/-- **Multiplication by the `i`-th Chern coefficient**, as a linear map out of the
top coefficient group.  This is the `g` of `ThomDeg.restrictMap`. -/
def chernMul {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ} (L : LerayHirschGraded π ξ r)
    (i : Fin r) :
    Hmod2 X (2 * r - 2 * r) →ₗ[ZMod 2] Hmod2 X (2 * r - 2 * (i : ℕ)) where
  toFun a := cohCast (by omega) (cup a (chernCoeff L i))
  map_add' a b := by
    show cohCast _ (cup (a + b) (chernCoeff L i)) = _
    rw [cup_add_left, cohCast_add]
  map_smul' c a := by
    show cohCast _ (cup (c • a) (chernCoeff L i)) = _
    rw [cup_smul_left, cohCast_smul]
    rfl

@[simp] theorem chernMul_apply {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) (i : Fin r) (a : Hmod2 X (2 * r - 2 * r)) :
    chernMul L i a = cohCast (by omega) (cup a (chernCoeff L i)) := rfl

/-! ## 4. The degreewise Chern relation -/

/-- **The top column term expands over the lower ones.**  This is the Chern
relation in the form the restriction square consumes: at the top degree `2r` the
index `r` is not part of a rank-`r` presentation, and the term it would carry is
the combination of the terms that are. -/
theorem lhTerm_top_eq_sum {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) (a : Hmod2 X (2 * r - 2 * r)) :
    lhTerm π ξ (2 * r) r a
      = ∑ i : Fin r, lhTerm π ξ (2 * r) (i : ℕ) (chernMul L i a) := by
  have hp : 2 * r - 2 * r + 2 * r = 2 * r := by omega
  have hdist : cup (pull π (2 * r - 2 * r) a)
        (∑ i : Fin r, lhTerm π ξ (2 * r) (i : ℕ) (chernCoeff L i))
      = ∑ i : Fin r, cup (pull π (2 * r - 2 * r) a)
          (lhTerm π ξ (2 * r) (i : ℕ) (chernCoeff L i)) := by
    exact map_sum (cupBilin P (2 * r - 2 * r) (2 * r) (pull π (2 * r - 2 * r) a))
      (fun i : Fin r => lhTerm π ξ (2 * r) (i : ℕ) (chernCoeff L i)) Finset.univ
  rw [lhTerm_of_le π ξ (le_refl (2 * r)), ← sum_lhTerm_chernCoeff L, hdist, cohCast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact cup_pull_lhTerm' π ξ (by have := i.isLt; omega) hp a (chernCoeff L i)

/-! Printed on every build. -/

#print axioms lhTerm_top_eq_sum

end ThomChernDeg

end

end GroupApproximation.CharClass
