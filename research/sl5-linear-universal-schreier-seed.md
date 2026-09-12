---
rg: 2
id: sl5-linear-universal-schreier-seed
kind: claim
title: Every small-defect SL5 tuple has a linear universal-host first vector
artifacts:
  - research/artifacts/sep7-padded-heat-linear-seed-self-improvement-2026-09-07.md
distinct_from:
  moving-subgroup-schreier-correction-has-no-index-loss: that proves constructions and consequences conditional on (MSC19); this asserts the open estimate (MSC19) itself.
  nonhyperlinear-sep7-logarithmic-seed: that admits a logarithmic loss in the squared spectral cutoff; this requires the linear cutoff, although the uniform assertions are equivalent by the padded heat theorem.
---

For the fixed elementary presentation of SL_5(Z), let delta(U) be
the maximum normalized-HS defining-relator defect of an
inverse-compatible tuple in U(n). Use the universal finite quotient
Q_(2n) and averaged rectangular coefficient Laplacian Delta from
`moving-subgroup-schreier-correction-has-no-index-loss`.

There exist L>0 and delta_*>0, independent of n and U, such that
every 0<delta(U)<delta_* satisfies

```text
min Spec Delta_(Q_(2n),U) <= L^2 delta(U)^2.
```

This is the open numerical assertion (MSC19), now separated from its
already established conditional consequences. Flexible SL5 stability
would imply it by the padded heat theorem. That conditional implication
does not establish either assertion.

## Attempts

Rectangular heat proves the estimate from a fixed coarse exact padded
comparison with target dimension at most 2n, regardless of how slowly
known corrections converge. Osgood extraction proves that a uniform
logarithmic seed would first supply flexible stability, which would
then supply this linear estimate. Neither argument produces the
initial comparison or first vector for an arbitrary approximate tuple.
The known compression constructions have such comparisons and
therefore cannot refute this estimate.
