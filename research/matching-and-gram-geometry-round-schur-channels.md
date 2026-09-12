---
rg: 2
id: matching-and-gram-geometry-round-schur-channels
kind: route
title: A maximal matching removes exceptional entries and Gram geometry makes the surviving split transitive
target: schur-near-idempotents-round-dimension-uniformly
requires: []
artifacts:
  - research/artifacts/schur-near-idempotent-partition-rounding-2026-09-08.md
---

Fix `0<t<1/10`. Make a graph whose bad edges are the pairs
with `|s_ij^2-s_ij|>t`. Test the idempotence-defect map on the
permutation matrix exchanging the endpoints of every edge in
a maximal matching. If `Z` is the set of these endpoints,

```text
|Z|/n <= delta^2/t^2.
```

Maximality makes `Z` a vertex cover, so every entry on the
remaining coordinates lies within `2t` of either zero or one.
The positive semidefinite correlation matrix is a Gram matrix
of unit vectors. Two entries at least `1/2` give vector
distances at most `2 sqrt(t)`, so the third entry is at least
`1-8t`. Since `1-8t>2t`, that third entry cannot be on the
zero side. Consequently `s_ij>=1/2` is an equivalence relation
off `Z`.

Take its equivalence classes as blocks and make every element
of `Z` a singleton block. The Schur symbols of `P_S` and the
associated conditional expectation differ by at most `2t`
off `Z` and by at most one on entries touching `Z`. Every
contraction has row and column squared sums at most one;
therefore the squared normalized-HS error is at most

```text
4t^2 + 2|Z|/n <= 4t^2 + 2delta^2/t^2.
```

For `0<delta<1/16`, use `t=sqrt(delta/7)`; the squared bound
is `(102/7)delta<16delta`. For larger `delta`, the diagonal
conditional expectation has distance at most one. At zero
defect, the entries are exactly zero or one and Gram geometry
directly supplies the partition. These arguments prove the
claim without a separate positivity-rounding assumption.
