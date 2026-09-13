---
rg: 2
id: complete-multipartite-raags-are-rips-type-r-proof
kind: route
title: Complete multipartite RAAGs are l^1 products of Cayley trees, so their Rips complexes are contractible
target: complete-multipartite-raags-are-rips-type-r
requires:
  - l1-products-of-trees-have-contractible-rips-complexes
---

1. A complete multipartite graph with parts `I_1, …, I_k` is the join
   `I_1 * ⋯ * I_k` of edgeless graphs. Vertices in different parts are
   adjacent, so they commute. Vertices in the same part are not adjacent, so
   they generate a free group. Hence `A_Γ = F_{n_1} × ⋯ × F_{n_k}`, and the
   largest clique has `k` vertices.
2. The standard generating set is the disjoint union of the free bases. For a
   direct product marked by the union of generating sets, the word length of
   `(g_1, …, g_k)` is `Σ_i |g_i|`. So the word metric is the l^1 product of the
   factor word metrics.
3. The word metric of `F_n` with a free basis is the path metric on the vertices
   of its Cayley graph, the `2n`-regular tree (for `n = 1`, the line). Degrees
   are bounded.
4. `l1-products-of-trees-have-contractible-rips-complexes` with
   `T_i = Cay(F_{n_i})` gives `R_t(A_Γ, V(Γ)) = VR_t(X)` contractible for
   `t ≥ k(k+1) − 1`.
