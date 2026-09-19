---
rg: 2
id: infinite-edge-first-chord-assembly
kind: route
title: Assemble the two relative spectral transports around the common chord sign
target: first-cycle-signed-hecke-chord
requires:
  - infinite-edge-common-commutant-for-first-chord
  - piecewise-group-transport-gives-corner-unitaries
---

For each endpoint, apply `(PGT1)--(PGT2)` to the matched partitions in
`(IEC2)--(IEC3)`.  This gives a corner unitary

```text
U_i=sum_(s,epsilon,k) g_(i,s,epsilon,k)p_(i,s,epsilon,k).
```

Because every source and range piece with index `s` lies under the same
separator atom, `U_i` commutes with every `e_(i,s)`.  It sends the positive
and negative spectral projections of `X_i` to those of `Z`, so

```text
U_i X_i U_i^*=Z.
```

Conjugate the whole endpoint context partition by `U_i`.  Predicate and
partition identities are invariant under conjugation, all parent-separator
marginals remain fixed, and both chord marginals become `Z`.  Every other
context is unchanged.  The survival clause in the required claim preserves a
non-root assignment projection.  This proves all clauses of the first-chord
claim.
