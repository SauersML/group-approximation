---
rg: 2
id: fpbs-hyperbolic-tiling-dual-clusters-bounded-from-pu
kind: claim
title: On hyperbolic regular tilings every dual cluster is bounded at every parameter from p_u on, and the dual threshold is one minus p_u
distinct_from:
  fpbs-critical-no-infinite-cluster: that is no infinite primal cluster at p_c on nonamenable quasi-transitive graphs; this is boundedness of all dual clusters on [p_u,1) for planar hyperbolic tilings, a statement about the primal uniqueness threshold p_u
---

**ESTABLISHED (import).** Let `G` be a regular tiling of the hyperbolic plane,
for example the `{4g,4g}` tiling that is the Cayley graph of the genus-`g`
surface group (`g >= 2`) with its standard generators. The **dual process** at
parameter `p` declares a dual edge `e†` open exactly when the primal edge `e`
is closed. So it is Bernoulli(`1-p`) bond percolation on the planar dual `G†`.

1. For every `p in [p_u(G), 1)` there is a unique unbounded primal cluster, and
   all clusters of the dual process are bounded, almost surely.
2. For `p in (p_c, p_u)` the dual process has infinitely many unbounded
   clusters. So `p_c(G†) = 1 - p_u(G)`, and `0 < p_c(G) < p_u(G) < 1`.

Source: I. Benjamini, O. Schramm, *Percolation in the hyperbolic plane*,
J. Amer. Math. Soc. 14 (2001), arXiv:math/9912233. Route:
`fpbs-hyperbolic-tiling-dual-clusters-bounded-from-pu-cite`.

Status records an imported theorem, not independent verification.
