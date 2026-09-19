import GroupApproximation.CharClass.BundleSplitCover
import GroupApproximation.CharClass.LerayHirschChartClassGen

/-!
# On its own open set, the tautological line is the summand

`cc-bundle`'s `tautLineIsoSummand` says that over the locus where a summand does
not kill the tautological line the two line bundles are isomorphic.  Euler classes
are invariant under isomorphism, so their Euler classes agree there.

That is the whole reason the split relation holds with the summands' Euler classes
as its roots, and it is why no tensor product and no additivity of the Euler class
is needed: over `ZMod 2` the factor `ξ + π^*e(L)` is also the difference, so it
vanishes exactly where the two classes agree.

Both Euler classes are taken in the index convention of `tautEulerOf`, pushed
forward along `tautEmbOf`, so nothing here reindexes and the comparison is between
two classes of the same type.

## Main declarations

* `lineEulerOf` — the Euler class of a line bundle, in `tautEulerOf`'s convention.
* `eulerOf_restrict_eq` — **the two agree on the open set.**
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.LH
open GroupApproximation.CharClass.CPn

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The Euler class of a line bundle, taken at the same index as `tautEulerOf`, so
that the two can be compared without a reindexing. -/
def lineEulerOf (q : Bundle X ι) (hq : ∀ x, (q x).trace = 1) : Hmod2 (TopCat.of X) 2 :=
  eulerOfBundle (show 1 ≤ 1 + tautCardOf ι by omega)
    (pushforward (tautEmbOf ι) (tautEmbOf_injective ι) q)
    (trace_pushforward_one (tautEmbOf ι) (tautEmbOf_injective ι) q hq)

/-- An isomorphism of bundles is carried along a pushforward of the index. -/
def pushforwardBundleIso {κ : Type} [Fintype κ] [DecidableEq κ] {A B : Bundle X ι}
    (f : ι → κ) (hf : Function.Injective f) (e : BundleIso A B) :
    BundleIso (pushforward f hf A) (pushforward f hf B) :=
  ((pushforwardIso f hf A).symm.trans e).trans (pushforwardIso f hf B)

/-- **On `lineOpenSet p q` the two Euler classes agree.**  The bundles are
isomorphic there by `cc-bundle`'s `tautLineIsoSummand`, and the Euler class is an
isomorphism invariant. -/
theorem eulerOf_restrict_eq (p q : Bundle X ι) (hq : ∀ x, (q x).trace = 1) :
    lineEulerOf (Bundle.restrictTo (tautLine p) (lineOpenSet p q))
        (fun y => trace_tautLine p (y : Proj p))
      = lineEulerOf (Bundle.restrictTo (comap (projPi p) q) (lineOpenSet p q))
        (fun y => hq (projPi p (y : Proj p))) :=
  eulerOfBundle_eq_of_bundleIso (show 1 ≤ 1 + tautCardOf ι by omega) _ _ _ _
    (pushforwardBundleIso (tautEmbOf ι) (tautEmbOf_injective ι)
      (tautLineIsoSummand p q hq))

end

end CharClass
end GroupApproximation
