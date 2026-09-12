import GroupApproximation.CharClass.ThomChernDegreewise
import GroupApproximation.CharClass.CohomologyLHDegreewiseOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The Chern relation, degreewise, over any commutative ring

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

`ThomChernDegreewise.lean` turns the Leray–Hirsch coefficient family of `ξ^r` into the
equation the restriction square consumes,

```text
lhTerm π ξ (2r) r a  =  ∑_{i < r} lhTerm π ξ (2r) i (γ_{r-i} ⌣ a),
```

at `F₂`.  The argument is cup-product bookkeeping: cupping a column term with a pulled-back
class of the base is again a column term.  It uses associativity, naturality and the degree
casts of the cup product, all generic, and the reindexing `LHCast.lhDomainEquivOf` of
`lix-coeff`.  No sign enters: the base class is cupped on the left of a column term, and
nothing is commuted past anything.

So the same proofs run over any commutative ring `K`.  These are new declarations beside
the `F₂` ones, with the `Of` suffix; `K` is implicit, determined by the Leray–Hirsch
instance.

## Main declarations

* `cup_pull_lhTermOf` — `π^*a ⌣ lhTerm π ξ n i b = lhTerm π ξ (p+n) i (a ⌣ b)`.
* `chernCoeffOf`, `chernMulOf` — the Chern coefficients and multiplication by them.
* `lhTerm_top_eq_sumOf` — **the degreewise Chern relation over `K`**.
-/

set_option autoImplicit false

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

namespace ThomChernDeg

open LH

set_option linter.unusedSectionVars false

variable {K : Type} [CommRing K] {X P : TopCat.{0}}

/-! ## 1. A degree transport across a finite sum -/

/-- `cohCast` commutes with a finite sum, over any commutative ring. -/
theorem cohCast_sumOf {m m' : ℕ} (h : m = m') {ι : Type} [Fintype ι]
    (F : ι → Hmod K X m) : cohCast h (∑ i, F i) = ∑ i, cohCast h (F i) := by
  subst h; rfl

/-! ## 2. Cupping a column term with a class of the base -/

/-- **A column term times a pulled-back class is a column term**, over any commutative
ring. -/
theorem cup_pull_lhTermOf (π : P ⟶ X) (ξ : Hmod K P 2) {p n i : ℕ} (hi : 2 * i ≤ n)
    (a : Hmod K X p) (b : Hmod K X (n - 2 * i)) :
    cup (pull π p a) (lhTerm π ξ n i b)
      = lhTerm π ξ (p + n) i
          (cohCast (by omega : p + (n - 2 * i) = p + n - 2 * i) (cup a b)) := by
  rw [lhTerm_of_le π ξ hi, lhTerm_of_le π ξ (show 2 * i ≤ p + n by omega),
    cup_cohCast_right, ← cup_assoc, ← pull_cup, cohCast_cohCast,
    pull_cohCast, cup_cohCast_left, cohCast_cohCast]

/-- The same with the ambient degree given by an equation. -/
theorem cup_pull_lhTermOf' (π : P ⟶ X) (ξ : Hmod K P 2) {p n m i : ℕ} (hi : 2 * i ≤ n)
    (hm : p + n = m) (a : Hmod K X p) (b : Hmod K X (n - 2 * i)) :
    cohCast hm (cup (pull π p a) (lhTerm π ξ n i b))
      = lhTerm π ξ m i (cohCast (by omega : p + (n - 2 * i) = m - 2 * i) (cup a b)) := by
  subst hm
  rw [cohCast_self]
  exact cup_pull_lhTermOf π ξ hi a b

/-! ## 3. The Chern coefficients, reindexed -/

/-- The coefficients of `ξ^r` in the Leray–Hirsch presentation over `K`, reindexed by
`Fin r`: `chernCoeffOf L i` is `γ_{r-i}`, in `H^{2r-2i}(X; K)`. -/
def chernCoeffOf {π : P ⟶ X} {ξ : Hmod K P 2} {r : ℕ} (L : LerayHirschGraded π ξ r)
    (i : Fin r) : Hmod K X (2 * r - 2 * (i : ℕ)) :=
  LHCast.lhDomainEquivOf K X r (2 * r) (lhDomainCard_two_mul r) L.gammaCoeff i

/-- **The defining relation, reindexed**: `ξ^r` is the combination of its own
coefficients. -/
theorem sum_lhTerm_chernCoeffOf {π : P ⟶ X} {ξ : Hmod K P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) :
    ∑ i : Fin r, lhTerm π ξ (2 * r) (i : ℕ) (chernCoeffOf L i) = cupPowE ξ r := by
  rw [← L.lhMap_gammaCoeff]
  exact (LHCast.lhMap_eq_sum_lhTermOf π ξ r (2 * r) (lhDomainCard_two_mul r)
    L.gammaCoeff).symm

/-- **Multiplication by the `i`-th Chern coefficient**, as a `K`-linear map out of the top
coefficient group.  This is the `g` of `ThomDeg.restrictMap` over `K`. -/
def chernMulOf {π : P ⟶ X} {ξ : Hmod K P 2} {r : ℕ} (L : LerayHirschGraded π ξ r)
    (i : Fin r) :
    Hmod K X (2 * r - 2 * r) →ₗ[K] Hmod K X (2 * r - 2 * (i : ℕ)) where
  toFun a := cohCast (by omega) (cup a (chernCoeffOf L i))
  map_add' a b := by
    show cohCast _ (cup (a + b) (chernCoeffOf L i)) = _
    rw [cup_add_left, cohCast_add]
  map_smul' c a := by
    show cohCast _ (cup (c • a) (chernCoeffOf L i)) = _
    rw [cup_smul_left, cohCast_smul]
    rfl

@[simp] theorem chernMulOf_apply {π : P ⟶ X} {ξ : Hmod K P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) (i : Fin r) (a : Hmod K X (2 * r - 2 * r)) :
    chernMulOf L i a = cohCast (by omega) (cup a (chernCoeffOf L i)) := rfl

/-! ## 4. The degreewise Chern relation -/

/-- **The top column term expands over the lower ones**, over any commutative ring. -/
theorem lhTerm_top_eq_sumOf {π : P ⟶ X} {ξ : Hmod K P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) (a : Hmod K X (2 * r - 2 * r)) :
    lhTerm π ξ (2 * r) r a
      = ∑ i : Fin r, lhTerm π ξ (2 * r) (i : ℕ) (chernMulOf L i a) := by
  have hp : 2 * r - 2 * r + 2 * r = 2 * r := by omega
  have hdist : cup (pull π (2 * r - 2 * r) a)
        (∑ i : Fin r, lhTerm π ξ (2 * r) (i : ℕ) (chernCoeffOf L i))
      = ∑ i : Fin r, cup (pull π (2 * r - 2 * r) a)
          (lhTerm π ξ (2 * r) (i : ℕ) (chernCoeffOf L i)) := by
    exact map_sum (cupBilin P (2 * r - 2 * r) (2 * r) (pull π (2 * r - 2 * r) a))
      (fun i : Fin r => lhTerm π ξ (2 * r) (i : ℕ) (chernCoeffOf L i)) Finset.univ
  rw [lhTerm_of_le π ξ (le_refl (2 * r)), ← sum_lhTerm_chernCoeffOf L, hdist, cohCast_sumOf]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact cup_pull_lhTermOf' π ξ (by have := i.isLt; omega) hp a (chernCoeffOf L i)

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms lhTerm_top_eq_sumOf

end ThomChernDeg

end

end GroupApproximation.CharClass
