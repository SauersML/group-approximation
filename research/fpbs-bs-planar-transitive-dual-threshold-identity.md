---
rg: 2
id: fpbs-bs-planar-transitive-dual-threshold-identity
kind: claim
title: On every transitive nonamenable one-ended planar graph the uniqueness threshold is one minus the dual critical threshold
distinct_from:
  fpbs-hyperbolic-tiling-dual-clusters-bounded-from-pu: that imports the three-phase picture from the abstract only, restricted to regular hyperbolic tilings; this imports Theorems 1.1 and 3.8 from the body of the paper for every transitive nonamenable planar graph with one end, including non-regular Cayley graphs such as Cay(Delta(2,3,7), {x, y, y^-1, xy, (xy)^-1}).
---

**ESTABLISHED (import).** Let `G` be a transitive, nonamenable, planar graph
with one end, and let `G†` be its planar dual. Then, for Bernoulli bond
percolation,

```text
p_c(G†) + p_u(G) = 1     and     0 < p_c(G) < p_u(G) < 1.
```

The dual `G†` is well defined up to isomorphism: by Proposition 2.1 of the
source, the embedding of such a `G` in the plane is unique up to reflection.
`G†` need not be transitive. It is quasi-transitive when `G` is a Cayley graph,
and it is locally finite, with degrees equal to the face sizes of `G`.

Source: I. Benjamini, O. Schramm, *Percolation in the hyperbolic plane*,
J. Amer. Math. Soc. 14 (2001), 487--507, arXiv:math/9912233, Theorems 1.1 and
3.8. Route: `fpbs-bs-planar-transitive-dual-threshold-identity-cite`.

Status records an imported theorem, not independent verification.
