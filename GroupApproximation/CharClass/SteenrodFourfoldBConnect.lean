import GroupApproximation.CharClass.SteenrodFourfoldBReindex

/-!
# Connecting the named families to the differentiated sum

The two blocks of the Leibniz rule each expand into three pieces, because the
boundary identity for `Φ` has three terms.  This file says which piece is which.

On the left, at splitting `p + 1`, the three pieces are the surviving left
family, the inner-swap family, and a face term.  On the right, at splitting `p`,
they are `B` itself at that splitting, the surviving right family, and a face
term.  The two surviving families are the ones that cancel; what is left is `B`
plus its inner swap plus the face terms, which is the identity being proved.

The only computation is that a power of the generator on top of a swap is the
next power, which is where the two families are seen to be the same expression.

## Main results

* `smul_pow_swapEnd` — a generator power on top of a swap is the next power.
* `padFour_split3_left`, `padFour_split3_right` — a block expands into its three
  pieces.
* `cancelA_succ_eq_smul_swap` — the surviving left family, written with the swap
  explicit, which is the form the left block produces.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- A power of the generator on top of a swap is the next power, because the
generator acts by the swap. -/
theorem smul_pow_swapEnd (X : TopCat.{0}) (m p : ℕ) (w : PairIdx X m →₀ ZMod 2) :
    (groupRingGen ^ p) • (swapEnd X m w) = (groupRingGen ^ (p + 1)) • w := by
  rw [← groupRingGen_smul X m w, ← mul_smul, ← pow_succ]

/-- The left block expands into its three pieces. -/
theorem padFour_split3_left (X : TopCat.{0}) (k a b : ℕ)
    (u₁ u₂ u₃ : PairIdx X a →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    padFour X k a b (u₁ + u₂ + u₃) v
      = padFour X k a b u₁ v + padFour X k a b u₂ v + padFour X k a b u₃ v := by
  rw [padFour_add_left, padFour_add_left]

/-- The right block expands into its three pieces, the generator power
distributing over them first. -/
theorem padFour_split3_right (X : TopCat.{0}) (k a b p : ℕ)
    (u : PairIdx X a →₀ ZMod 2) (v₁ v₂ v₃ : PairIdx X b →₀ ZMod 2) :
    padFour X k a b u ((groupRingGen ^ p) • (v₁ + v₂ + v₃))
      = padFour X k a b u ((groupRingGen ^ p) • v₁)
        + padFour X k a b u ((groupRingGen ^ p) • v₂)
        + padFour X k a b u ((groupRingGen ^ p) • v₃) := by
  rw [smul_add, smul_add, padFour_add_right, padFour_add_right]

/-- **The surviving left family, with the swap explicit.**  This is the form the
left block of the Leibniz rule produces, and seeing it as `cancelA` is what makes
it cancel against the right block. -/
theorem cancelA_succ_eq_smul_swap (X : TopCat.{0}) (k i c d p : ℕ)
    (ρ : singularSimplices X c) (τ : singularSimplices X d) :
    cancelA X k i c d ρ τ (p + 1)
      = padFour X k (c + p) (d + (i - p)) (phiAtDeg X (c + p) p ρ)
          ((groupRingGen ^ p) • swapEnd X (d + (i - p))
            (phiAtDeg X (d + (i - p)) (i - p) τ)) := by
  show padFour X k (c + p) (d + (i - p)) (phiAtDeg X (c + p) p ρ)
      ((groupRingGen ^ (p + 1)) • phiAtDeg X (d + (i - p)) (i - p) τ) = _
  rw [smul_pow_swapEnd]

end

end Steenrod
end CharClass
end GroupApproximation
