---
rg: 2
id: free-memory-injectivity-bijectivity-proof
kind: route
title: Invert the encoder over the surjunctive cover and push the inverse down along the homomorphism
target: free-memory-injectivity-forces-universal-bijectivity
requires: []
artifacts:
  - research/artifacts/bijective-forcing-of-table-cores-2026-09-12.md
---

Section 7 of the artifact.

1. Over the surjunctive cover `H` the injective encoder is bijective. Its inverse is a
   cellular automaton (Curtis–Hedlund–Lyndon). It acts coset by coset, so it has
   memory inside `<rho_H(M)>`.
2. Transport the inverse's memory along `phi` with the same rule. Products that are
   equal in `H` stay equal in `G`. So both composite tables over `G` dominate the
   sufficient tables over `H`, and coarsening preserves sufficiency. The encoder over
   `G` therefore has a two-sided inverse.
3. The free group on the memory letters is residually finite, hence surjunctive, and
   maps compatibly onto every realization. That gives the free-memory corollary.
