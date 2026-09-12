import GroupApproximation.CharClass.CohomologyAssoc

/-!
# Lane `sp-coeff`: axiom check and the `ZMod 2` identification

A leaf file, imported by nothing, kept out of the import closure of the tree on
purpose so that adding to it never forces a rebuild.  It records two things.

**1. The `F₂` instance is the vendored object, not a copy.**  `cup` and `one`
at `K = ZMod 2` are *definitionally* the vendored `cupZMod2` and `oneZMod2`
(the three further bridges — for the cohomology object, the cocycle class and
the pullback — are in `CoeffCohomology.lean`, where downstream files need them).

**2. The generic layer uses no axiom beyond the three standard ones.**
-/

open GroupApproximation.CharClass
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

example {X : TopCat.{0}} {p q : ℕ} (a : Hmod2 X p) (b : Hmod2 X q) :
    cup a b = cupZMod2 a b := rfl

example (X : TopCat.{0}) : (one X : Hmod2 X 0) = oneZMod2 X := rfl

#print axioms GroupApproximation.CharClass.aw_cochain_leibniz
#print axioms GroupApproximation.CharClass.cochainCup_respects_cocycles
#print axioms GroupApproximation.CharClass.cochainCup_coboundary_right'
#print axioms GroupApproximation.CharClass.cupK_mk
#print axioms GroupApproximation.CharClass.cohPullbackK_cupK
#print axioms GroupApproximation.CharClass.cup_one
#print axioms GroupApproximation.CharClass.pull_cup
#print axioms GroupApproximation.CharClass.cup_assoc
#print axioms GroupApproximation.CharClass.one_cup
