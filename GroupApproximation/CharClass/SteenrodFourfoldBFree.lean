import GroupApproximation.CharClass.SteenrodFourfoldBDegen

/-!
# The summand with every degree free

The friction in assembling the chain map is not mathematical: it is that the same
natural number arrives spelled differently at each junction, `i + 1 - (p + 1)`
against `i - p`, `c + (p + 1)` against `c + p + 1`, and none of those pairs is
syntactic even though all are definitional.

The cure is the one that removed the degree casts from this lane in the first
place, applied one level further: **let the summand take all four of its degrees
as free parameters**, so that no arithmetic appears in the middle of the
computation at all.  `phiAtDeg` already takes its total degree freely and
`padFour` already absorbs the degree constraint, so the summand can be written
with the two module degrees and the two resolution indices independent, and the
arithmetic relating them pushed out to the single place where the sum is formed.

Every intermediate step is then a statement about free parameters, and the
successor forms the Leibniz rule needs are available on the nose rather than
after a conversion.

## Main results

* `bTerm` — the summand, with all four degrees free.
* `tensorD_bTerm` — its differential, split into blocks.
* `padFourL_bTerm_succ`, `padFourR_bTerm_succ` — each block at a successor
  degree, with no arithmetic to reconcile.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- **The summand of `B`, with every degree free.**  `a` and `b` are the two
module degrees, `p` and `q` the two resolution indices, and nothing relates them;
the relations are imposed once, outside, where the sum is formed. -/
noncomputable def bTerm (X : TopCat.{0}) (k a b p q : ℕ) {c d : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X d) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  padFour X k a b (phiAtDeg X a p ρ) ((groupRingGen ^ p) • phiAtDeg X b q τ)

/-- The summand of `B` is the free-degree summand at the degrees the sum
supplies. -/
theorem compBPre_eq_bTerm (X : TopCat.{0}) (k i p N : ℕ) (r : PairIdx X N) :
    compBPre X k i p N r
      = bTerm X k (r.1.val.1 + p) (r.1.val.2 + (i - p)) p (i - p) r.2.1 r.2.2 := rfl

/-- The differential of the free-degree summand, split into its two blocks. -/
theorem tensorD_bTerm (X : TopCat.{0}) (k a b p q : ℕ) {c d : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X d) :
    tensorD (pairFreeCx X) (pairFreeCx X) k (bTerm X (k + 1) a b p q ρ τ)
      = padFourL X k a b (phiAtDeg X a p ρ)
            ((groupRingGen ^ p) • phiAtDeg X b q τ)
        + padFourR X k a b (phiAtDeg X a p ρ)
            ((groupRingGen ^ p) • phiAtDeg X b q τ) :=
  tensorD_padFour X k a b _ _

/-- The left block at a successor module degree.  With the degree free there is
nothing to reconcile: the successor form the Leibniz rule needs is the one
written. -/
theorem padFourL_bTerm_succ (X : TopCat.{0}) (k a' b p q : ℕ) {c d : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X d) :
    padFourL X k (a' + 1) b (phiAtDeg X (a' + 1) p ρ)
        ((groupRingGen ^ p) • phiAtDeg X b q τ)
      = padFour X k a' b (dTgt X (ZMod 2) a' (phiAtDeg X (a' + 1) p ρ))
          ((groupRingGen ^ p) • phiAtDeg X b q τ) :=
  padFourL_succ_eq' X k a' b _ _

/-- The right block at a successor module degree, with the generator power moved
past the differential. -/
theorem padFourR_bTerm_succ (X : TopCat.{0}) (k a b' p q : ℕ) {c d : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X d) :
    padFourR X k a (b' + 1) (phiAtDeg X a p ρ)
        ((groupRingGen ^ p) • phiAtDeg X (b' + 1) q τ)
      = padFour X k a b' (phiAtDeg X a p ρ)
          ((groupRingGen ^ p) • dTgt X (ZMod 2) b' (phiAtDeg X (b' + 1) q τ)) := by
  rw [padFourR_succ_eq', dTgt_smul]

end

end Steenrod
end CharClass
end GroupApproximation
