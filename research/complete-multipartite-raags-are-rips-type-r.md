---
rg: 2
id: complete-multipartite-raags-are-rips-type-r
kind: claim
title: RAAGs on complete multipartite graphs (products of free groups) are of Rips type R with r_0 = k(k+1) − 1
distinct_from:
  raags-with-clique-or-triangle-free-components-are-type-r: that covers free products of free abelian groups and two-dimensional RAAGs; this covers direct products of free groups of any rank in any dimension, e.g. F_2 × F_2 × F_2
---

Let `Γ` be a complete multipartite graph with parts of sizes
`n_1, …, n_k ≥ 1`, so `A_Γ = F_{n_1} × ⋯ × F_{n_k}` and `k` is the dimension
of `A_Γ`. Then `R_t(A_Γ, V(Γ))` is contractible for every integer
`t ≥ k(k+1) − 1`.

Examples: `F_2 × F_2 × F_2` and `Z^2 × F_2` (`K_4` minus an edge), both from
`t ≥ 11`, which were open in dimension 3 before this; and `Z^n` (all parts of
size 1), recovering Zaremsky's bound.

UNREVIEWED (it rests on
`l1-products-of-trees-have-contractible-rips-complexes`). Proof: route
`complete-multipartite-raags-are-rips-type-r-proof`.
