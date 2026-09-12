---
rg: 2
id: spherical-relation-quadruple-counts
kind: claim
title: Spherical relation quadruples have uniform degrees and negligible repeated-slot codegrees
---

Fix a finite unitary table in dimension `d` and let `p_d` be the measure of a
radius-one cap in the unit sphere of `C^d`.  Sample `N=N(d)` independent
uniform sphere points and, for every tested unitary label `w`, write

```text
A_w(i,j)=1[ ||U_w x_i-x_j|| <= 1 ].
```

For each tested relation `gh=k`, form the four-partite relation hypergraph with
edges `(i,j,l,m)` satisfying

```text
A_h(i,j) A_g(j,l) A_k(i,m)=1.
```

One may choose `N(d)` so that, with probability tending to one simultaneously
over the finite table:

- every one-colour in-degree and out-degree is `(1+o(1))N p_d`;
- every vertex of every relation hypergraph has degree
  `(1+o(1))N^3 p_d^3`; and
- every codegree obtained by fixing at least two of the four coloured slots is
  `o(N^3 p_d^3)`.

No trace separation or multiplicative-defect estimate is needed for this
repeated-slot counting statement.  The freedom to take `N` arbitrarily large
lets one impose both `N p_d >> log N` and `N p_d^3 -> infinity`.  Distinct-word
same-output cap intersections are the separate geometric issue already closed
by `spherical-fixed-order-cap-codegrees`.
