---
rg: 2
id: raags-with-multipartite-or-triangle-free-components-type-r-proof
kind: route
title: Free-product closure applied to complete multipartite and triangle-free components
target: raags-with-multipartite-or-triangle-free-components-type-r
requires:
  - complete-multipartite-raags-are-rips-type-r
  - triangle-free-raags-are-rips-type-r
  - rips-type-r-closed-under-finite-edge-group-splittings
---

The same induction as `raags-with-clique-or-triangle-free-components-are-type-r-proof`.
`A_Γ` is the free product of the component RAAGs, with the union of their
standard generating sets. Each component RAAG is of type R: complete
multipartite components by `complete-multipartite-raags-are-rips-type-r`,
triangle-free components by `triangle-free-raags-are-rips-type-r`. Iterating
the amalgam clause of `rips-type-r-closed-under-finite-edge-group-splittings`
with trivial edge group `C = 1`, whose generating-set hypothesis is vacuous,
gives type R for the free product.
