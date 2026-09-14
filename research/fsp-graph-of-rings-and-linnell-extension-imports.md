---
rg: 2
id: fsp-graph-of-rings-and-linnell-extension-imports
kind: claim
title: Over every division ring, Hughes-free vertex rings embed graphs of groups in division rings, and Hughes-free kernels give Linnell embeddings of elementary amenable extensions
distinct_from:
  fisher-sanchez-peralta-special-and-3-manifold-domains: that imports Theorem 1.3 of the same paper, on special and 3-manifold groups; this imports the characteristic-free tools of its Sections 2 and 3, the graph-of-rings corollary and the elementary amenable extension corollary, with the standard facts the paper quotes about Hughes-free division rings.
  linear-sterility-does-not-obstruct-division-embedding: that uses the paper's characteristic-zero Proposition 3.14 on Higman's group; this imports the general statements behind it, which hold over every division ring.
artifacts:
  - research/artifacts/gk3-nonrf-hosts-2026-09-14.md
---

**ESTABLISHED (literature import)** by [[fsp-graph-of-rings-and-linnell-extension-citation]].

Throughout, `k` is an arbitrary division ring, so every characteristic is allowed, and `k*G` is a crossed
product; the group ring `k[G]` is the untwisted case. Definitions are those of the source:

* **Hughes-free.** For locally indicable `G`, an injective epic `k*G`-division ring `D` is Hughes-free if,
  whenever `H <= G` is finitely generated and `N ⊴ H` with `H/N = <tN> ≅ Z`, the powers `t^n` are left
  linearly independent over `Div(k*N, D)`. When it exists it is written `D_{k*G}`.
* **Linnell.** For torsion-free `G`, an epic embedding `k*G -> D` is Linnell if for every subgroup `H <= G`
  every right transversal of `H` in `G` is left linearly independent over `Div(k*H, D)`.

The imported statements:

1. **Uniqueness and restriction.** If `G` is locally indicable, a Hughes-free division ring of `k*G` is unique
   up to `k*G`-isomorphism (Hughes). For `H <= G`, the division closure of `k*H` in `D_{k*G}` is Hughes-free
   for `k*H`.
2. **Existence for known classes (Jaikin-Zapirain).** If `G` is locally indicable amenable, residually
   torsion-free nilpotent, or free-by-cyclic, then `D_{k*G}` exists. RAAGs, and so free groups, are residually
   torsion-free nilpotent.
3. **Linnell gives Hughes-free.** If `G` is locally indicable and `k*G -> D` is Linnell, it is Hughes-free.
4. **Automorphisms extend.** If `H ⊴ G` is locally indicable and `D_{k*H}` exists, the conjugation action of
   `G` extends to `D_{k*H}`, so the crossed product `D_{k*H} * [G/H]` exists and contains `k*G`.
5. **Elementary amenable extensions.** Let `G` be torsion-free, `H ⊴ G` locally indicable with `G/H`
   elementary amenable. If `D_{k*H}` exists and `D_{k*H} * [G/H]` is a domain, then
   `k*G -> Ore(D_{k*H} * [G/H])` is a Linnell embedding.
6. **Graphs of groups.** Let `G` be the fundamental group of a graph of locally indicable groups `(G_v, G_e)`.
   If `k*G_v` has a Hughes-free embedding for every vertex `v`, then `k*G` embeds in a division ring.

Item 6 is characteristic-free in the source. Its application to Higman's group there (Proposition 3.14) is
stated only in characteristic zero, because the vertex groups `BS(1,2) *_Z BS(1,2)` were given Hughes-free
division rings through the characteristic-zero Strong Atiyah theorem.
