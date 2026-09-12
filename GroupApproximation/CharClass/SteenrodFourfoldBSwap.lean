import GroupApproximation.CharClass.SteenrodFourfoldBTransport

/-!
# The surviving family is the inner swap of `B`

Differentiating one term of `B` produces four families.  Two of them coincide
after the reindexing `p ↦ p + 1` and cancel in characteristic two.  Of the two
survivors, one is `B` one resolution index down, which is visible; the other is
the one this file identifies.

It comes from the `T` half of the boundary identity applied to the front factor,
so it carries a swap on the first block and a power of the generator one higher
on the second.  That is exactly the action which swaps *inside* each block,
applied to `B` one index down: the swap on the second block is the extra power of
the generator, because the generator acts by that swap.

Once that is said, the low terms of the computation are `B + (inner swap of B)`,
and the transport carries `inner swap` to `block swap`, which is the `(1 + t)`
half of the source differential.  So this is the identification the whole
cancellation turns on.

## Main results

* `tenHom_swapHom_padFour` — the inner swap acts on a totalised decomposable
  factorwise.
* `swapEnd_smul_pow` — a swap on top of a generator power is the next power.
* `innerSwapFour_compBPre` — **the surviving family is the inner swap of the
  term**.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- The inner swap acts on a totalised decomposable one block at a time. -/
theorem tenHom_swapHom_padFour (X : TopCat.{0}) (k a b : ℕ)
    (u : PairIdx X a →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    innerSwapFour X k (padFour X k a b u v)
      = padFour X k a b (swapEnd X a u) (swapEnd X b v) := by
  by_cases h : a + b = k
  · rw [padFour_of_eq h, padFour_of_eq h]
    exact tenHom_tenElt (swapHom (singFreeCx X)) (swapHom (singFreeCx X)) k a b h u v
  · rw [padFour_of_ne h, padFour_of_ne h]
    exact map_zero (innerSwapFour X k)

/-- A swap on top of a power of the generator is the next power, because the
generator acts by the swap. -/
theorem swapEnd_smul_pow (X : TopCat.{0}) (m p : ℕ)
    (w : PairIdx X m →₀ ZMod 2) :
    swapEnd X m ((groupRingGen ^ p) • w) = (groupRingGen ^ (p + 1)) • w := by
  rw [← groupRingGen_smul X m ((groupRingGen ^ p) • w), ← mul_smul, ← pow_succ']

/-- **The surviving family is the inner swap of the term.**  The `T` half of the
boundary identity on the front factor is a swap on the first block, and the
matching power of the generator one higher on the second block is the swap
there. -/
theorem innerSwapFour_compBPre (X : TopCat.{0}) (k i p N : ℕ) (r : PairIdx X N) :
    innerSwapFour X k (compBPre X k i p N r)
      = padFour X k (r.1.val.1 + p) (r.1.val.2 + (i - p))
          (swapEnd X (r.1.val.1 + p) (phiAtDeg X (r.1.val.1 + p) p r.2.1))
          ((groupRingGen ^ (p + 1))
            • phiAtDeg X (r.1.val.2 + (i - p)) (i - p) r.2.2) := by
  show innerSwapFour X k
      (padFour X k (r.1.val.1 + p) (r.1.val.2 + (i - p))
        (phiAtDeg X (r.1.val.1 + p) p r.2.1)
        ((groupRingGen ^ p) • phiAtDeg X (r.1.val.2 + (i - p)) (i - p) r.2.2)) = _
  rw [tenHom_swapHom_padFour, swapEnd_smul_pow]

end

end Steenrod
end CharClass
end GroupApproximation
