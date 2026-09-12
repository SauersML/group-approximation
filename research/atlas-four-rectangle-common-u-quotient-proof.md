---
rg: 2
id: atlas-four-rectangle-common-u-quotient-proof
kind: route
title: Compute the biclique cycle basis and apply independent edge-fiber gauges
target: atlas-four-rectangles-do-not-descend-to-common-u
requires:
  - atlas-a4-packet-biclique-decomposition
  - atlas-a4-packet-four-rectangle-normal-form
  - atlas-common-u-is-twelve-double-coset-system
  - atlas-shifted-factorizations-have-independent-right-gauge
---

The rank formula `(FRD2)` and the explicit spanning-tree gauge in
`unitary-k2m-rectangle-synchronization` give exactly the four words `(FRD3)`.
A simple bipartite graph has girth at least four, proving their minimal word
length.  The usual fundamental-cycle theorem generates every closed walk
from this basis.

The common-frame theorem supplies `(FRD4)` and the independent gauges
`(FRD5)`.  Substitution of `M_e=L_e=U` in `(FRD3)` gives

```text
UU^*UU^*=I
```

on every basis cycle.  Conversely, if an edge message is extracted from one
factor, changing only the gauge of a non-tree edge leaves all common products
fixed but inserts that gauge into exactly one occurrence of its fundamental
cycle.  Taking the gauge to be `exp(it)I` rotates the whole cycle spectrum.
Hence no spectral function of that word is well defined on the common-frame
quotient.

Finally `(FRD6)` says that each edge lies in the reference double coset.
Every invariant under its left and right centralizer actions is constant on
that orbit, proving the local principal-angle assertion.  These observations
exhaust the degree-four graph holonomies and establish the claimed fence.
