import GroupApproximation.CharClass.SteenrodFourfoldBEdgeSwap

/-!
# The degenerate bidegree contributes only at splitting zero

At the bidegree where the cut puts nothing in the front face, the left block of
the Leibniz rule vanishes at every splitting, which was already recorded.  This
file completes that picture: the *right* block vanishes there too at every
positive splitting, because its untouched factor is the diagonal of a
`0`-simplex at a positive index, and there is no cut set that large.

So at the degenerate bidegree the whole computation reduces to the zeroth
splitting, where the right block contributes the composite and its inner swap —
the swap because the diagonal of a `0`-simplex is fixed by it — and no face term
at all, since a `0`-simplex has no faces.

That is the identity at this bidegree, with none of the reindexing needed.

## Main results

* `padFourL_of_zero_right`, `padFourR_of_zero_left` — a block vanishes when the
  factor it does *not* differentiate is zero.
* `padFourR_degenerate_succ` — at the degenerate bidegree, the right block
  vanishes at every positive splitting.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- A block vanishes when the factor it does not differentiate is zero. -/
theorem padFourL_of_zero_right (X : TopCat.{0}) (k a b : ℕ)
    (u : PairIdx X a →₀ ZMod 2) :
    padFourL X k a b u 0 = 0 := by
  cases a with
  | zero => exact padFourL_zero_deg X k b u 0
  | succ a' =>
      rw [padFourL_succ_eq']
      exact padFour_zero_right k a' b _

/-- The mirror: the right block vanishes when its untouched factor is zero. -/
theorem padFourR_of_zero_left (X : TopCat.{0}) (k a b : ℕ)
    (v : PairIdx X b →₀ ZMod 2) :
    padFourR X k a b 0 v = 0 := by
  cases b with
  | zero => exact padFourR_zero_deg X k a 0 v
  | succ b' =>
      rw [padFourR_succ_eq']
      exact padFour_zero_left k a b' _

/-- **At the degenerate bidegree the right block also vanishes at every positive
splitting.**  Its untouched factor is the diagonal of a `0`-simplex at a positive
index, and a `0`-simplex has no cut set that large.  With the left block already
known to vanish there, the whole computation at this bidegree is the zeroth
splitting. -/
theorem padFourR_degenerate_succ (X : TopCat.{0}) (k b p : ℕ)
    (ρ : singularSimplices X 0) (v : PairIdx X b →₀ ZMod 2) (hp : 0 < p) :
    padFourR X k (0 + p) b (phiAtDeg X (0 + p) p ρ) v = 0 := by
  rw [phiAtDeg_eq_zero_of_lt X (0 + p) p 0 ρ hp]
  exact padFourR_of_zero_left X k (0 + p) b v

end

end Steenrod
end CharClass
end GroupApproximation
