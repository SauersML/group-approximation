import GroupApproximation.CharClass.SteenrodFourfoldBoundary

/-!
# The one place the pair complex's differential is named

`padFourL` and `padFourR` are defined through `cc-cartan`'s `tdL` and `tdR`, so
that nothing in the Leibniz rule forces the structure projection
`(pairFreeCx X).d`; forcing it makes the elaborator time out, because
`tensorFreeCx` is a structure literal whose square-zero field is a large proof.

But the chain-map computation for `B` has to apply the boundary identity for `Φ`
to the differentiated factor, and that identity is stated for `dTgt`.  So the
projection has to be named exactly once.  This file is that once, and it is kept
in its own module so that a failure here blocks nothing else.

## Main results

* `pairFreeCx_d_eq` — the projection, evaluated.
* `padFourL_succ_eq`, `padFourR_succ_eq` — each half of the Leibniz rule in the
  form the computation consumes: a `padFour` of the differentiated factor.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- The differential of the pair complex, as a `FreeCx`, is the tensor
differential of the singular complex with itself. -/
theorem pairFreeCx_d_eq (X : TopCat.{0}) (a : ℕ) :
    (pairFreeCx X).d a = tensorD (singFreeCx X) (singFreeCx X) a := rfl

/-- **The left half of the Leibniz rule**, with the differentiated factor named
as `dTgt`. -/
theorem padFourL_succ_eq (X : TopCat.{0}) (k a' b : ℕ) (h : a' + 1 + b = k + 1)
    (u : PairIdx X (a' + 1) →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    padFourL X k (a' + 1) b u v = padFour X k a' b (dTgt X (ZMod 2) a' u) v := by
  have hab : a' + b = k := by omega
  rw [padFourL_of_eq h, tdL_succ (pairFreeCx X) (pairFreeCx X) k a' b h u v,
    pairFreeCx_d_eq, tensorD_eq_dTgt X a' u]
  exact (padFour_of_eq hab (dTgt X (ZMod 2) a' u) v).symm

/-- **The right half of the Leibniz rule.** -/
theorem padFourR_succ_eq (X : TopCat.{0}) (k a b' : ℕ) (h : a + (b' + 1) = k + 1)
    (u : PairIdx X a →₀ ZMod 2) (v : PairIdx X (b' + 1) →₀ ZMod 2) :
    padFourR X k a (b' + 1) u v = padFour X k a b' u (dTgt X (ZMod 2) b' v) := by
  have hab : a + b' = k := by omega
  rw [padFourR_of_eq h, tdR_succ (pairFreeCx X) (pairFreeCx X) k a b' h u v,
    pairFreeCx_d_eq, tensorD_eq_dTgt X b' v]
  exact (padFour_of_eq hab u (dTgt X (ZMod 2) b' v)).symm

/-! ## The forms the computation consumes

The double sum defining `B` runs over degrees that are not known to satisfy the
degree constraint, so the two halves are wanted **without** a hypothesis: off the
diagonal both sides are `0`, for the same reason. -/

theorem padFourL_succ_eq' (X : TopCat.{0}) (k a' b : ℕ)
    (u : PairIdx X (a' + 1) →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    padFourL X k (a' + 1) b u v = padFour X k a' b (dTgt X (ZMod 2) a' u) v := by
  by_cases h : a' + 1 + b = k + 1
  · exact padFourL_succ_eq X k a' b h u v
  · rw [padFourL_of_ne h, padFour_of_ne (show ¬ a' + b = k by omega)]

theorem padFourR_succ_eq' (X : TopCat.{0}) (k a b' : ℕ)
    (u : PairIdx X a →₀ ZMod 2) (v : PairIdx X (b' + 1) →₀ ZMod 2) :
    padFourR X k a (b' + 1) u v = padFour X k a b' u (dTgt X (ZMod 2) b' v) := by
  by_cases h : a + (b' + 1) = k + 1
  · exact padFourR_succ_eq X k a b' h u v
  · rw [padFourR_of_ne h, padFour_of_ne (show ¬ a + b' = k by omega)]

/-- **The Leibniz rule in consumable form**: the differential of a totalised
decomposable, with each half already expressed as a `padFour` of the
differentiated factor.  Both halves are hypothesis-free. -/
theorem tensorD_padFour_succ (X : TopCat.{0}) (k a b : ℕ)
    (u : PairIdx X (a + 1) →₀ ZMod 2) (v : PairIdx X (b + 1) →₀ ZMod 2) :
    tensorD (pairFreeCx X) (pairFreeCx X) k (padFour X (k + 1) (a + 1) (b + 1) u v)
      = padFour X k a (b + 1) (dTgt X (ZMod 2) a u) v
        + padFour X k (a + 1) b u (dTgt X (ZMod 2) b v) := by
  rw [tensorD_padFour, padFourL_succ_eq', padFourR_succ_eq']

end

end Steenrod
end CharClass
end GroupApproximation
