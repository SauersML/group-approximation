---
rg: 2
id: fpbs-mohar-adjacency-norm-cheeger-bound
kind: claim
title: The adjacency norm of a regular graph is bounded by its edge expansion through the Mohar inequality
distinct_from:
  fpbs-regular-tiling-edge-isoperimetric-constant: that computes the edge expansion of planar regular graphs with regular dual; this bounds the adjacency operator norm of any regular graph in terms of its edge expansion.
  fpbs-expansion-thinning-threshold: that bounds p_c by the edge expansion; this bounds the spectral radius, and so the walk-counting lower bound on p_{2->2}, by the same constant.
artifacts:
  - research/artifacts/fpbs/docs/expanding-factor-product-thresholds.md
---

**ESTABLISHED (import).** Let `G` be an infinite connected `d`-regular graph with
edge expansion `h = inf{ |∂_E K|/|K| : K finite nonempty }`. Then the adjacency
operator satisfies

```text
||A_G||_{2->2}  <=  sqrt(d^2 - h^2).
```

This is the upper half of Theorem 6.7 of Lyons–Peres, *Probability on Trees and
Networks*, `1 - rho(G) >= 1 - sqrt(1 - Phi_E(G)^2)`, incorporating Mohar (1988).
There `rho(G) = ||P||` and `Phi_E(G) = Phi_E(G;1;deg) = h/d` for an unweighted
`d`-regular graph. Route: `fpbs-mohar-adjacency-norm-cheeger-bound-citation`.
