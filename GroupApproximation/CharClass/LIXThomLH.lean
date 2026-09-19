import GroupApproximation.CharClass.LIXThomDatum
import GroupApproximation.CharClass.CohomologyLHDegreewise

/-!
# The Leray–Hirsch coefficients at the top degree, as a linear equivalence

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`cc-cohom-api`'s `LHCast.bijective_sum_lhTerm_top` gives, from a Leray–Hirsch
instance at rank `r+1`, that the coefficient combination is a **bijection** onto
`H^{2r}` of the projectivisation.  This file packages it as a linear equivalence,
which is the form the Thom-class algebra consumes.

## What this does and does not discharge

It discharges, by one application of their theorem, the identification of the
coefficient product with the **absolute** group `H^{2r}(P(E⊕1))`.

It does **not** discharge the second hypothesis of `LIXThomDatum`.  That
hypothesis is about the **relative** group of the pair `(P(E⊕1), P(E⊕1) ∖ Z)`,
and Leray–Hirsch says nothing relating the two.  Unpacked against the equivalence
below, what is still needed is

* `relToAbs` injective — exactness of the pair sequence, `cc-relative`'s;
* `range relToAbs = ker absToSub` — the same sequence one step on;
* and `absToSub` identified with `ThomDeg.restrictMap g`, which is
  `cc-projective`'s tautological restriction together with
  `ThomChernBasis.genPow_dim_eq_neg_basisSum`.

All four inputs exist.  Composing them is a further assembly, not a consequence
of the equivalence, and stating otherwise is the mistake this file's docstring
exists to prevent.

## Main declarations

* `lhCoeffTop` — the coefficient family at the top degree.
* `lhSumTop` — the coefficient combination, as a linear map.
* `lhTopEquiv` — **it is a linear equivalence**, by one application of
  `LHCast.bijective_sum_lhTerm_top`.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.CharClass.LH

namespace GroupApproximation.CharClass

noncomputable section

variable {X P : TopCat.{0}}

/-- The Leray–Hirsch coefficient group in slot `i` at the top degree. -/
abbrev lhCoeffTop (X : TopCat.{0}) (r : ℕ) (i : Fin (r + 1)) : Type :=
  Hmod2 X (2 * r - 2 * (i : ℕ))

/-- The coefficient combination at the top degree, as a linear map. -/
def lhSumTop (π : P ⟶ X) (ξ : Hmod2 P 2) (r : ℕ) :
    ((i : Fin (r + 1)) → lhCoeffTop X r i) →ₗ[ZMod 2] Hmod2 P (2 * r) where
  toFun a := ∑ i : Fin (r + 1), lhTerm π ξ (2 * r) (i : ℕ) (a i)
  map_add' a b := by
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => lhTerm_add π ξ (2 * r) (i : ℕ) (a i) (b i)
  map_smul' c a := by
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · simp [lhTerm_zero]
    · simp

@[simp] theorem lhSumTop_apply (π : P ⟶ X) (ξ : Hmod2 P 2) (r : ℕ)
    (a : (i : Fin (r + 1)) → lhCoeffTop X r i) :
    lhSumTop π ξ r a = ∑ i : Fin (r + 1), lhTerm π ξ (2 * r) (i : ℕ) (a i) := rfl

/-- **The coefficient product is the absolute top cohomology.**  One application
of `cc-cohom-api`'s `bijective_sum_lhTerm_top`, packaged linearly. -/
noncomputable def lhTopEquiv {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ (r + 1)) :
    ((i : Fin (r + 1)) → lhCoeffTop X r i) ≃ₗ[ZMod 2] Hmod2 P (2 * r) :=
  LinearEquiv.ofBijective (lhSumTop π ξ r) (LHCast.bijective_sum_lhTerm_top L)

/-! Printed on every build. -/

#print axioms lhTopEquiv

end

end GroupApproximation.CharClass
