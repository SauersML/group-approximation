---
rg: 2
id: finite-graph-of-groups-representation-types-are-integer-flows
kind: claim
title: Finite graph-of-groups representation types are positive integer flows through restriction maps
artifacts:
  - research/artifacts/a4-context-virtually-free-compiler-2026-08-19.md
---

Let `G` be a finite graph of finite groups.  For each vertex `v`, write a
finite-dimensional unitary representation type as its nonnegative integer
multiplicity vector in the basis `Irr(G_v)`.  For each oriented edge, restrict
the two adjacent vertex types to the finite edge group and subtract.
Collecting these maps gives a fixed integer linear operator

```text
d_G : Theta_V -> Theta_E.
```

Then the vertex multiplicity vectors of finite-dimensional representations of
the fundamental group are **exactly**

```text
Theta_V^+ intersect ker(d_G).
```

Conversely every positive integer point in this kernel is realized by a global
unitary representation.  After normalizing by total dimension, all possible
discrete representation-type data therefore lie in a fixed rational polytope;
matrix size appears only through the denominator of a rational point.
