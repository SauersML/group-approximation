---
rg: 2
id: titz-witzel-same-building-sofic-donor-collapses-proof
kind: route
title: Use the computed full automorphism group and finite-index rigidity of the smallest lattice
target: titz-witzel-same-building-sofic-donor-collapses
requires:
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
---

Titz Mite--Witzel, *Non-residually finite `C~_2`-lattices*,
arXiv:2509.05054v2, Proposition 4.11, compute

```text
Aut(X)=barGamma,              Aut(X)^type=K,             [barGamma:K]=2.
```

In particular `Aut(X)` is discrete.  A lattice in a discrete locally
compact group has finite index, so `Lambda` has finite index in `barGamma`.
Consequently `Lambda cap K` has finite index in `K`.  Theorem 4.1 of the
same paper proves that `K` has no proper finite-index subgroup.  Since `K`
is infinite, `Lambda cap K` cannot be trivial and therefore equals `K`.
Thus

```text
K <= Lambda <= barGamma,
```

and the index-two quotient leaves only the two displayed possibilities.
Soficity is invariant under passage to finite-index subgroups and
overgroups, so either one is sofic exactly when the other is.  End proof.
