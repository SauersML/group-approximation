import GroupApproximation.CharClass.LerayHirschNaturalCoeff
import GroupApproximation.CharClass.ChernSliceNaturality

/-!
# Leray–Hirsch coefficients under a base change of bundles

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, items 3 and 4).

`lhCoeff_natural_eq` computes the coefficients of a restricted class over an
abstract square.  For a projectivised bundle the square is not abstract: it is
`projComap_square`, and the degree-two class transports by `tautEulerOf_comap`.
Both are landed, so at a base change of bundles the naturality has no hypotheses
left beyond the two Leray–Hirsch instances.

**Restriction to a subspace of the base is this lemma.**  `Bundle.restrictTo p U`
*is* `comap` along the subtype inclusion, so a consumer restricting to a
trivialising ball, or to the fibre over a point, instantiates `f` and nothing else.
At a one-point base the instance downstairs is `lerayHirschGraded_compact` with
nothing added, and every coefficient below the top then sits in a positive degree
of a point and dies.

## Main declarations

* `lhCoeff_comap` — **the coefficients of a restricted class, at a base change of
  bundles.**

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory
open GroupApproximation.CharClass.Bundle

noncomputable section

set_option linter.unusedSectionVars false

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The Leray–Hirsch coefficients of a class restricted along a base change.**

The two instances are the only inputs: the commuting square and the transport of
the tautological class are supplied by this lane rather than hypothesised, because
in the projection model both are landed facts about `projComap`.

Bundle restriction is the case `f = Subtype.val`, since `Bundle.restrictTo` is
`comap` along that inclusion. -/
theorem lhCoeff_comap (f : C(Y, X)) (q : Bundle X ι) {s : ℕ}
    (L : LerayHirschGraded (projMapOf q) (tautEulerOf q) s)
    (L' : LerayHirschGraded (projMapOf (comap f q)) (tautEulerOf (comap f q)) s)
    (n : ℕ) (z : Hmod2 (TopCat.of (Proj q)) n) :
    L'.lhCoeff n (pull (cmap (projComap f q)) n z)
      = fun i : Fin (lhDomainCard s n) =>
          pull (cmap f) (n - 2 * (i : ℕ)) (L.lhCoeff n z i) :=
  lhCoeff_natural_eq (cmap f) (cmap (projComap f q)) (projMapOf q)
    (projMapOf (comap f q)) (projComap_square f q) (tautEulerOf q)
    (tautEulerOf (comap f q)) (tautEulerOf_comap f q) L L' n z

end

end LH
end CharClass
end GroupApproximation
