---
rg: 2
id: fpbs-product-every-generating-set-via-percolation-kesten
kind: route
title: Products via the percolation Kesten gap along the second factor
target: fpbs-product-every-generating-set
requires:
  - fpbs-percolation-kesten-normal-gap
  - fpbs-relative-gap-along-any-subgroup-separates
---

Let `G = H x K` with `H` nonamenable and `K` infinite, and let `S` be any finite
symmetric generating set. The subgroup `N = 1 x K` is infinite and normal, and
`G/N ≅ H` is nonamenable. `fpbs-percolation-kesten-normal-gap` gives
`p_c(Cay(G,S)) < p_c(N;Cay(G,S))`.
`fpbs-relative-gap-along-any-subgroup-separates` then gives `p_c < p_u`. ∎

Nothing is assumed about `K` beyond being infinite. So the route covers
`T x T'` and `B(m,n) x B(m',n')`, where every amenable subgroup is finite and
the amenable-kernel routes are unavailable.
