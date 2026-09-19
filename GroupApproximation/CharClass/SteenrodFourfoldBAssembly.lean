import GroupApproximation.CharClass.SteenrodFourfoldBAtDeg

/-!
# Assembling the chain map: splitting the differentiated sum

The differential of `B` at a fixed bidegree is a sum over the splitting of the
resolution index, and each summand splits by the Leibniz rule into a left block
and a right block.  This file separates the two, which is the first step of the
assembly: the left blocks and the right blocks are then reindexed against each
other, two of the four families coincide, and they cancel.

Everything here is linearity.  The content of the assembly is in the reindexing
that follows, not in this separation.

## Main result

* `sum_tensorD_padFour_split` — the differentiated sum as the sum of the left
  blocks plus the sum of the right blocks.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- **The differentiated sum splits into its two blocks.**  Each summand splits
by the Leibniz rule and the sum of a pointwise sum is the sum of the sums. -/
theorem sum_tensorD_padFour_split (X : TopCat.{0}) (k n : ℕ)
    (a b : ℕ → ℕ)
    (u : ∀ p : ℕ, PairIdx X (a p) →₀ ZMod 2)
    (v : ∀ p : ℕ, PairIdx X (b p) →₀ ZMod 2) :
    (∑ p ∈ Finset.range n,
        tensorD (pairFreeCx X) (pairFreeCx X) k
          (padFour X (k + 1) (a p) (b p) (u p) (v p)))
      = (∑ p ∈ Finset.range n, padFourL X k (a p) (b p) (u p) (v p))
        + ∑ p ∈ Finset.range n, padFourR X k (a p) (b p) (u p) (v p) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => tensorD_padFour X k (a p) (b p) (u p) (v p)

end

end Steenrod
end CharClass
end GroupApproximation
