import GroupApproximation.CharClass.SteenrodFourfoldBConnect

/-!
# The edge bidegree cancels for a different reason

At the bidegree where the cut puts nothing in the front face, the left block of
the Leibniz rule vanishes outright, so the surviving swap family cannot come from
it.  It comes from the right block instead, and the reason is that **the diagonal
of a `0`-simplex is symmetric**: `Φ₀(x) = x ⊗ x`, which the factor swap fixes.

So at that bidegree the term the right block contributes with the higher power of
the generator is not cancelled against anything; it *is* the inner-swap term of
the identity, because swapping the front factor changes nothing.

This is worth isolating.  The pairing of the two surviving families, which cancels
them, is valid only away from this bidegree, and an assembly that assumed it
everywhere would be wrong in exactly the place where the diagonal degenerates.

## Main result

* `swapEnd_phiAtDeg_degree_zero` — the diagonal of a `0`-simplex is fixed by the
  swap.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- **The diagonal of a `0`-simplex is symmetric.**  `Φ₀(x)` is `x ⊗ x`, and the
factor swap fixes it.  This is why, at the bidegree with nothing in the front
face, the surviving swap family comes from the right block rather than from the
left, which vanishes there. -/
theorem swapEnd_phiAtDeg_degree_zero (X : TopCat.{0}) (ρ : singularSimplices X 0) :
    swapEnd X 0 (phiAtDeg X 0 0 ρ) = phiAtDeg X 0 0 ρ := by
  rw [phiAtDeg_eq_sum, Finset.sum_range_one, swapEnd_cellPair,
    tensorSwap_steenrodDiag_degree_zero]

/-- The same, said of `Φ₀` directly. -/
theorem swapEnd_phiZero_degree_zero (X : TopCat.{0}) (ρ : singularSimplices X 0) :
    swapEnd X 0 (phiZero X 0 ρ) = phiZero X 0 ρ :=
  swapEnd_phiAtDeg_degree_zero X ρ

end

end Steenrod
end CharClass
end GroupApproximation
