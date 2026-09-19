---
rg: 2
id: finite-depth-prefix-hard-sign-proof
kind: route
title: Centralize the earlier pulse subgroup in each finite-depth HNN row
target: finite-depth-prefix-preserving-hard-sign-hnn
requires: []
---

By `(FDP1)` and independence of the `B_k`, the assignment

```text
A_n |-> B_n,          B_k |-> B_k  (k<n)
```

is an isomorphism between two elementary-abelian subgroups.  Britton normal
form therefore embeds the base at every iterated HNN step.  The second family
in `(FDP2)` makes `V_n` commute with every factor of `(FDP3)`, proving
`(FDP4)`.  The first relation gives

```text
B_nV_nP_n=V_nA_nP_n=-V_nP_n,
```

which is `(FDP5)`.  Orthogonality of the first-negative prefix projections
is the elementary telescope

```text
C_n=C_(n+1)+C_n(1-B_n)/2.
```

In an approximate representation, each projection in `(FDP3)` is a product
of `n` commuting sign cuts.  The standard product telescope is linear in
`n`; summing the finitely many covariance defects in `(FDP2)` proves the
robust statement.

