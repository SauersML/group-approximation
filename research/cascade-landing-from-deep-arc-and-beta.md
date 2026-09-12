---
rg: 2
id: cascade-landing-from-deep-arc-and-beta
kind: claim
title: The cascade landing property follows from two residual predicates over a C'(1/6) family
distinct_from:
  bespoke-routing-lemma: that is the router interface and its frozen conclusion list; this is a statement about the descent argument a router's relator family is fed to, and it names no family at all.
  greendlinger-free-product-lemma: that is the free-product form of Greendlinger's lemma; this is the cascade descent over a single free group, whose conclusion is a located Greendlinger arc or a landing.
artifacts:
  - GroupApproximation/Sofic/GreendlingerCascade.lean
  - GroupApproximation/Sofic/GreendlingerBetaBranch.lean
  - GroupApproximation/Sofic/GreendlingerAlphaPlumb.lean
---

For a set of relators `R` over an alphabet,

```text
MetricSmallCancellation R (1/6)
  and DeepArcSource R
  and LandingProductionBeta R
        ==>  CascadeLanding R.
```

This is `cascadeLanding_of_deepArc_of_beta`.  `CascadeLanding` is the statement
that a minimal conjugacy expression, cut at a window, either exhibits a located
Greendlinger arc on the outside or lands inside the block --- it is the descent
step the whole router lane runs on.

Upstream of the plumbing there is a cleaner two-input form,
`cascadeLanding_of_deepArc_of_landing`, which takes `DeepArcSource` and
`LandingProduction` and **no metric hypothesis at all**;
`landingProduction_of_beta` is what spends `C'(1/6)` to get from
`LandingProductionBeta` to `LandingProduction`.

## Where the remaining difficulty sits

Neither residual is proved.  `DeepArcSource` is only ever reduced further ---
`deepArcSource_of_deepTailArc`, `deepArcSource_of_deepOverrunArc` --- and every
producer takes another residual as input.  `LandingProductionBeta` is not
produced anywhere in the half-form lane; it appears only as a hypothesis.  Its
sharp twin `LandingProductionBetaSharp` *is* produced, but again from a
residual (`StoppingAlternativeBetaSharp`).

So the honest reading is: the descent lane is fully assembled and its
remaining content is two named word-combinatorial statements, not a proof
strategy.

## Do not count C'(1/6) as an open leaf

`MetricSmallCancellation R (1/6)` is the lane's standing side condition on the
family, supplied by whichever relator family is plugged in --- it is discharged
for the router's own family through `metric_eighth` and monotonicity.  Counting
it as a third *open* input overstates what is left; counting the theorem as
two-input while forgetting it understates what the statement assumes.  It has
two open residuals and one side condition.
