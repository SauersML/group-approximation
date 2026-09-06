import GroupApproximation.CharClass.LerayHirschNatural

/-!
# The Leray–Hirsch coefficients of a restricted class

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, items 3 and 4).

`LerayHirschNatural` states naturality as a uniqueness principle: a family whose
combination is the restricted class *is* the restricted family.  That is the right
shape for a consumer holding a family already, and the wrong one for a consumer
who wants to compute the coefficients of a restriction.  This file is the second
shape, with both Leray–Hirsch instances supplied so that nothing is hypothesised.

The only content beyond `lhCoeff_natural` is that both coefficient families are
already known to combine to the class they came from, so the hypothesis discharges
itself.

## Main declarations

* `lhCoeff_natural_eq` — **the coefficients of a restriction are the restrictions
  of the coefficients.**

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable {X X' P P' : TopCat.{0}}

/-- **The coefficients of a restriction are the restrictions of the coefficients.**

Both Leray–Hirsch instances are supplied, so this computes rather than constrains.
The base downstairs is arbitrary: for a contractible one every coefficient below
the top sits in a positive degree and dies, which is how a top-coefficient
argument survives restriction. -/
theorem lhCoeff_natural_eq (f : X' ⟶ X) (g : P' ⟶ P) (π : P ⟶ X) (π' : P' ⟶ X')
    (hsq : g ≫ π = π' ≫ f) (ξ : Hmod2 P 2) (ξ' : Hmod2 P' 2)
    (hξ : pull g 2 ξ = ξ') {r : ℕ} (L : LerayHirschGraded π ξ r)
    (L' : LerayHirschGraded π' ξ' r) (n : ℕ) (z : Hmod2 P n) :
    L'.lhCoeff n (pull g n z)
      = fun i : Fin (lhDomainCard r n) =>
          pull f (n - 2 * (i : ℕ)) (L.lhCoeff n z i) :=
  lhCoeff_natural f g π π' hsq ξ ξ' hξ r n (L'.bij n).injective
    (L.lhCoeff n z) (L'.lhCoeff n (pull g n z))
    (by rw [L'.lhMap_lhCoeff, L.lhMap_lhCoeff])

end

end LH
end CharClass
end GroupApproximation
