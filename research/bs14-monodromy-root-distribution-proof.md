---
rg: 2
id: bs14-monodromy-root-distribution-proof
kind: route
title: Distribute the inverse monodromy root over every cyclic edge
target: bs14-long-packet-monodromy-reset-creates-fixed-sources
requires:
  - bs14-unitary-representations-are-periodic-cycle-packets
  - bs14-trivial-boundary-inversion-forces-r-fixed-source
---

Because `W` is a function of `V`, the edge product after the replacement is
`VW^m=1`.  Edge weights do not affect the covariance with the scalar
`S`-weights, proving `(LMR2)`.  Every edge changes by a unitary translate of
`W-1`, so their orthogonal matrix supports give the first equality in
`(LMR3)`.  Functional calculus and
`2|sin(theta/(2m))|<=|theta|/m` give the inequalities.

For a direct sum of packets with `m>=M`, sum `(LMR3)` and divide by total
dimension:

```text
sum pi^2 k/m <= (pi^2/M^2) sum m k.
```

Taking square roots gives the global `pi/M` bound.  Since the new monodromy
is the identity, `(TET1)` identifies its `k` fixed vectors.

