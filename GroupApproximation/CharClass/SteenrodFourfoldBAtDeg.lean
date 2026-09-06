import GroupApproximation.CharClass.SteenrodFourfoldBSplit

/-!
# The summand at a fixed bidegree

Splitting `B` by the bidegree of the cut makes the front degree an explicit
summation index, but the summand still refers to it through the basis element:
`compBPre` reads the degrees off `r`, and inside a linear combination Lean has no
way to know that every `r` in the support has the bidegree the index names.

This file removes that.  At a fixed bidegree the injection into the pair index is
a `mapDomain`, and a linear combination along a `mapDomain` is a linear
combination of the composite, so the injection can be pushed into the summand.
After that the degrees in the summand are the summation indices themselves,
written out, and the case analysis the Leibniz rule needs is finally available on
them.

## Main result

* `compBPre_at_bidegree` — the summand of `B` at a fixed bidegree, with its
  degrees written out rather than read off the basis element.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- **The summand at a fixed bidegree.**  The left side reads the two degrees off
the basis element; the right side has them as the given naturals `c` and `d`.
The two are the same because the injection at a fixed bidegree is a `mapDomain`,
and a linear combination along one is a linear combination of the composite. -/
theorem compBPre_at_bidegree (X : TopCat.{0}) (k i p N c d : ℕ) (h : c + d = N)
    (z : tensorTwo X c d) :
    Finsupp.linearCombination (ZMod 2) (compBPre X k i p N) (cellPair X N c d z)
      = Finsupp.linearCombination (ZMod 2)
          (fun q : singularSimplices X c × singularSimplices X d =>
            padFour X k (c + p) (d + (i - p))
              (phiAtDeg X (c + p) p q.1)
              ((groupRingGen ^ p) • phiAtDeg X (d + (i - p)) (i - p) q.2)) z := by
  rw [cellPair_of_eq h, Finsupp.linearCombination_mapDomain]
  rfl

end

end Steenrod
end CharClass
end GroupApproximation
