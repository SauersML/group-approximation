---
rg: 2
id: infinite-irs-finite-index-trace-proof
kind: route
title: Intersect every infinite random subgroup with the finite-index actor subgroup
target: infinite-irs-characters-defeat-finite-haar-tags
requires: []
---

Fix a finite-index subgroup `K<=Gamma`.  For every infinite subgroup
`H<=Gamma`, the map from left cosets of `H intersect K` in `H` to left cosets
of `K` in `Gamma` is injective.  Hence

```text
[H:H intersect K] <= [Gamma:K].                           (IFP1)
```

Thus `H intersect K` is infinite and contains a nonidentity element.  Since
`mu` is supported on infinite subgroups,

```text
1
=mu({H:H is infinite})
<=mu(union_(k in K minus {e}) {H:k in H}).                 (IFP2)
```

The group `K` is countable.  If every membership cylinder in the union had
measure zero, the union would have measure zero.  Therefore some `k!=e` in
`K` satisfies

```text
chi_mu(k)=mu({H:k in H})>0.                               (IFP3)
```

So the restriction to `K` is not regular.  Taking
`K=ker(eta)` for a finite-image tag homomorphism proves the finite-Haar-tag
consequence through the canonical-trace criterion of
`haar-tag-cancellation-retention-is-group-realizability`.
