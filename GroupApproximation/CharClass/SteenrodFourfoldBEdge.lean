import GroupApproximation.CharClass.SteenrodFourfoldBAssembly

/-!
# The edge bidegrees of the assembly

Two whole families drop out of the assembly before any reindexing.  When the cut
of `σ` puts nothing in the front face, the left block of the Leibniz rule
contributes nothing at any splitting of the resolution index: at splitting `0`
because there is no boundary to take in degree zero, and at every positive
splitting because a `0`-simplex has no cut set that large.  Dually on the right.

Removing them first is what makes the reindexing that follows a statement about
two families rather than four.

## Main results

* `padFourL_eq_zero_of_front`, `padFourR_eq_zero_of_back` — a block vanishes when
  its own degree is zero, stated so the degree may be zero only propositionally.
* `sum_padFourL_front_zero`, `sum_padFourR_back_zero` — the two edge families.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- The left block vanishes when its degree is zero, even when that is known only
propositionally. -/
theorem padFourL_eq_zero_of_front {X : TopCat.{0}} {k a b : ℕ} (h : a = 0)
    (u : PairIdx X a →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    padFourL X k a b u v = 0 := by
  subst h
  exact padFourL_zero_deg X k b u v

/-- The right block vanishes when its degree is zero. -/
theorem padFourR_eq_zero_of_back {X : TopCat.{0}} {k a b : ℕ} (h : b = 0)
    (u : PairIdx X a →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    padFourR X k a b u v = 0 := by
  subst h
  exact padFourR_zero_deg X k a u v

/-- **The left edge family vanishes.**  With nothing in the front face there is
no boundary to take at splitting `0`, and no cut set large enough at any positive
splitting. -/
theorem sum_padFourL_front_zero (X : TopCat.{0}) (k n b : ℕ)
    (ρ : singularSimplices X 0) (v : ℕ → (PairIdx X b →₀ ZMod 2)) :
    (∑ p ∈ Finset.range n, padFourL X k (0 + p) b (phiAtDeg X (0 + p) p ρ) (v p)) = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  cases p with
  | zero => exact padFourL_eq_zero_of_front rfl _ (v 0)
  | succ p' =>
      exact padFourL_term_eq_zero X k 0 (p' + 1) b ρ (v (p' + 1)) (by omega)

/-- **The right edge family vanishes**, by the mirror argument.  The power of the
generator does not save it: the group ring acts by a linear involution. -/
theorem sum_padFourR_back_zero (X : TopCat.{0}) (k n a : ℕ)
    (u : ℕ → (PairIdx X a →₀ ZMod 2)) (q : ℕ → ℕ)
    (τ : singularSimplices X 0) :
    (∑ p ∈ Finset.range n,
        padFourR X k a (0 + q p) (u p)
          ((groupRingGen ^ p) • phiAtDeg X (0 + q p) (q p) τ)) = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  rcases Nat.eq_zero_or_pos (q p) with hq | hq
  · exact padFourR_eq_zero_of_back (by omega) (u p) _
  · exact padFourR_term_eq_zero X k a 0 p (q p) (u p) τ hq

end

end Steenrod
end CharClass
end GroupApproximation
