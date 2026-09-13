---
rg: 2
id: cograph-raags-are-rips-type-r
kind: claim
title: RAAGs on P4-free graphs have contractible Rips complexes for all scales t ≥ k(k+1) − 1, k the clique number
distinct_from:
  complete-multipartite-raags-are-rips-type-r: that covers products of free groups only; this covers every graph built by joins and disjoint unions, e.g. Z × (Z^2 * Z)
  raags-with-multipartite-or-triangle-free-components-type-r: that adds triangle-free components through a cited free-product theorem; this handles free products and direct products uniformly, with explicit scale k(k+1) − 1, but not triangle-free graphs containing an induced P4
---

Let `Γ` be a finite graph with no induced path on four vertices (a cograph),
with clique number `k ≥ 1`. Then `R_t(A_Γ, V(Γ))` is contractible for every
integer `t ≥ k(k+1) − 1`.

Newly covered (dimension ≥ 3, containing a triangle, not complete
multipartite): `Z × (Z^2 * Z)` (triangle with a pendant vertex),
`(F_2 × Z^2) * Z^3`, `Z × ((F_2 × F_2) * Z)`.

UNREVIEWED. Proof: route `cograph-raags-are-rips-type-r-proof`.

Still open: graphs containing a triangle and an induced P4, e.g. the cone
`K_1 * P4`, where `A_Γ = Z × A_{P4}`.
