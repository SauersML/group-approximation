---
rg: 2
id: gersten-free-algebra-k-theory
kind: claim
title: Gersten - the free algebra over a noetherian regular ring has the K-theory of its coefficients
distinct_from:
  regular-coherent-coefficients-kill-leavitt-tensor-k-theory: that computes K-theory of Leavitt tensor algebras through Ara--Brustenga--Cortinas; this is Gersten's computation for the free algebra itself, the ring before any Leavitt relation is imposed.
---

**ESTABLISHED by citation** (`gersten-free-algebra-k-theory-citation`). Let `k` be a noetherian regular
ring and `k{X}` the free `k`-algebra on a set `X`. Then the inclusion `k -> k{X}` induces
`K_*(k) ≅ K_*(k{X})`.

In degree 2 this is Milnor's `K_2 = ker(St -> E)`, by Weibel IV Corollary 1.7.1 (quoted in the
citation route). The cases used in the graph are `k = Z` and `k = F_p`, where

```text
K_2(Z<x_1..x_k>) = K_2(Z),        K_2(F_p<x_1..x_k>) = K_2(F_p) = 0.
```

The second vanishing is `quillen-k-theory-of-finite-fields`.
