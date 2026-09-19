---
rg: 2
id: finite-moment-random-relator-sparsification-proof
kind: route
title: Finite profile union bound proves all-dimensions sparsification
target: finite-moment-random-relator-sparsification
requires:
  - finite-trace-profile-net-is-dimension-free
artifacts:
  - research/artifacts/nonhyperlinear-finite-moment-sparsification-2026-08-18.md
---

For one net profile `z in Z`, independence of the `m` sampled relators gives
probability exactly `p(z)^m <= q^m` that every sampled relator is
`eps_plus`-small at `z`.  The union bound over the finite net therefore gives
probability at most `N q^m` that any net profile passes all checks.

Now suppose an actual `delta`-separated finite-dimensional tuple has profile
`x in K_delta` and every sampled relator has defect at most `eps`.  Choose
`z in Z` with `||x-z||_infinity <= eta`.  For every sampled relator `r`,

```text
2 - 2 z_r
 <= (2 - 2 x_r) + 2 eta
 <= eps^2 + 2 eta
 < eps_plus^2.
```

Thus `z` passes every sampled relator at the enlarged threshold, so existence
of the actual tuple implies one of the finitely many net events already counted.
This proves the probability bound simultaneously over all matrix dimensions.

If `Pr(SC)>N q^m`, the preservation event cannot be contained in the bad event,
so some sampled relator tuple lies in `SC` while admitting no separated
`eps`-microstate.  No dimension limit or representation-stratum decomposition
enters the proof.
