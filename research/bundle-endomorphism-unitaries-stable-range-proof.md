---
rg: 2
id: bundle-endomorphism-unitaries-stable-range-proof
kind: route
title: Stiefel connectivity, relative obstruction theory and the gauge fibration
target: bundle-endomorphism-unitaries-stable-range
requires: []
artifacts:
  - research/artifacts/stw59-unique-trace-and-matrix-stability-2026-09-05.md
---

Section 3 of the linked artifact (internally reviewed on 5 September 2026)
proves this lemma. The steps:

1. The space of fiberwise isometric embeddings `H -> F ⊕ H` has fibers
   `U(r+s)/U(r)`, which are `2r`-connected.
2. Relative cellular obstruction theory makes the section space
   `(2r - d)`-connected.
3. The polar lift `T = wv* + (1-Q)(1-P)` gives a locally trivial principal
   bundle `G(F) -> G(F ⊕ H) -> S(H, F ⊕ H)`.
4. Its exact sequence proves `pi_k G(F) -> pi_k G(F ⊕ H)` is an isomorphism
   when `d + k + 1 <= 2r`.

Iterating with `H = F` over `nF` and applying Bott periodicity identifies the
stable limit with `K_(k+1)`. The artifact states the lemma for exactly the
canonical stable map, as recorded in the target.
