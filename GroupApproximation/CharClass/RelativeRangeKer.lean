import GroupApproximation.CharClass.RelativeLES

/-!
# Exactness of the pair sequence as `range = ker`

`RelativeLES.lean` exports exactness at the absolute group in element form
(`relLES_exact_abs`: a class restricting to zero on the subspace comes from a
relative class).  Several consumers — `cc-thom`'s `topChernClass_ne_zero_odd_iso`
and the chain data `cc-lix-odd` assembles — take it instead as the equality of a
range and a kernel.  That conversion needs the short complex `pairShortComplex`
and its `homology_exact₂`, which is internal plumbing of this lane, so it is
published here rather than reconstructed at the call sites.

It is one application of Mathlib's `ShortComplex.Exact.moduleCat_range_eq_ker` to
the short exact sequence of the pair.

## Main results

* `relLES_range_eq_ker` — `range j^* = ker i^*` in every degree.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- **Exactness at `H^n(X)` as an equality of submodules.**  The image of `j^*` is
the kernel of `i^*`. -/
theorem relLES_range_eq_ker (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    LinearMap.range (relToAbs (ZMod 2) X A n).hom
      = LinearMap.ker (absToSub (ZMod 2) A n).hom :=
  ((pairShortExact (ZMod 2) X A).homology_exact₂ n).moduleCat_range_eq_ker

/-- The same over an arbitrary commutative ring of coefficients. -/
theorem relLES_range_eq_ker' (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    LinearMap.range (relToAbs R X A n).hom = LinearMap.ker (absToSub R A n).hom :=
  ((pairShortExact R X A).homology_exact₂ n).moduleCat_range_eq_ker

end

end GroupApproximation.CharClass
