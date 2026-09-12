import GroupApproximation.Sofic.GreendlingerSharpWindow
import GroupApproximation.Sofic.GreendlingerSharpResidualWiring

/-!
# The sharp residual bundle, reduced to the window level

`SharpResiduals` is the two-field hypothesis that gates the whole routing lane.
Its `deep` field asks for `DeepOverrunArcSharp`, a statement about arcs,
rotations and relator membership.  This file replaces that demand by the
strictly more elementary `DeepOverrunWindowSharp`, which asks only where two
cancellations leave a window inside one word.

The chain is entirely made of theorems that already exist, plus the one link
added in `GreendlingerSharpWindow`:

```
DeepOverrunWindowSharp                                   -- the new obligation
  → DeepOverrunLandingSharp    (deepOverrunLandingSharp_of_windowSharp, new)
  → DeepOverrunArcSharp        (deepOverrunArcSharp_of_landingSharp, existing)
  → SharpResiduals.deep
```

## What this is and is not

`sharpResiduals_of_windowSharp_of_betaSharp` is a **reduction**, not a
discharge.  It consumes two families and produces the bundle; nothing here
proves either family.  The point is that the `deep` obligation a prover now
has to meet is the window one, and the window statement mentions no
`GreendlingerAtSharp`, no `symmetrization` membership for the arc, and no
rotation --- those were all discharged upstream by
`greendlingerAtSharp_of_rotation_window`.

The `beta` family is passed through untouched.  It is the other open leaf, and
this file makes no claim about it.

The `λ`-free lane has exactly the same shape: `DeepOverrunWindow` reduces to
`DeepOverrunLanding` reduces to `DeepOverrunArc`, and the window predicate is
open there too.  So this is the sharp mirror of an architecture that was
already chosen, not a new route.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-- **The sharp deep obligation, from the sharp window obligation.**

Composition of the new reduction with the existing frame.  Neither step reads
the small-cancellation hypothesis: the frame passes the two `λ`-carrying
fields through untouched, and the window producer was already twinned. -/
theorem deepOverrunArcSharp_of_windowSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (h : DeepOverrunWindowSharp R lam) : DeepOverrunArcSharp R lam :=
  deepOverrunArcSharp_of_landingSharp hR hRne
    (deepOverrunLandingSharp_of_windowSharp h)

/-- **The bundle, from the window family and the beta family.**

This is `SharpResiduals` with its `deep` obligation weakened to the window
level.  A construction that wants the sharp gate --- and hence the router, and
hence a routed quotient --- may now supply a window family instead of an arc
family.

Both arguments are hypotheses.  This theorem creates no obligation and
discharges none; it moves one of the two. -/
theorem sharpResiduals_of_windowSharp_of_betaSharp [DecidableEq α]
    (hwin : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 → MetricSmallCancellation R lam →
      DeepOverrunWindowSharp R lam)
    (hbeta : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 → MetricSmallCancellation R lam →
      LandingProductionBetaSharp' R lam) :
    SharpResiduals α where
  deep := fun R lam hcyc hRne hlam0 hlam hmetric =>
    deepOverrunArcSharp_of_windowSharp hcyc hRne
      (hwin R lam hcyc hRne hlam0 hlam hmetric)
  beta := hbeta

end SmallCancellationRouter
end GroupApproximation
