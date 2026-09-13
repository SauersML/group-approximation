---
rg: 2
id: based-dehn-nielsen-baer-for-closed-surfaces
kind: claim
title: For a closed orientable surface of genus at least two, Aut(pi_1) is the extended mapping class group of the once-marked surface, and pi_1 has trivial center
distinct_from:
  punctured-surface-mcgs-satisfy-permutational-boone-higman: that imports the permutational Boone--Higman property for mapping class groups of punctured surfaces; this is the classical identification of the automorphism group of a closed surface group with one of those groups.
artifacts:
  - research/artifacts/solve-bh-3manifold-2026-09-13.md
---

**ESTABLISHED (textbook import)** through `based-dehn-nielsen-baer-citation`.

Let `S_g` be the closed orientable surface of genus `g >= 2` and let `S_(g,1)`
be the same surface with one marked point. Then:

1. `pi_1(S_g)` has trivial center, so `Inn(pi_1(S_g)) = pi_1(S_g)`;
2. choosing the marked point as basepoint gives an isomorphism
   `Mod^±(S_(g,1)) -> Aut(pi_1(S_g))`.

Here `Mod^±(S_(g,1))` is the extended mapping class group of the surface with
one marked point, which is the extended mapping class group of the
once-punctured surface.
