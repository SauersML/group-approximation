---
rg: 2
id: type-fn-groups-have-n-minus-1-connected-rips-complexes
kind: claim
title: Every group of type F_n has an (n-1)-connected Rips complex for some generating set and scale
distinct_from:
  some-type-fn-group-has-no-n-minus-1-connected-rips-complex: that is the negation, a specific group of type F_n all of whose Rips complexes fail (n-1)-connectivity; this is the universal positive statement
---

For every `n >= 1` and every group `G` of type `F_n` there are a finite
generating set `S` of `G` and a scale `t >= 0` such that the Rips complex
`R_t(G,S)` is (n−1)-connected.

Equivalently (`group-rips-complexes-are-cayley-graph-flag-complexes`): every
group of type `F_n` has a finite symmetric generating set `T` such that the
clique complex of `Cay(G,T)` is (n−1)-connected. This is the affirmative
answer to Zaremsky Problem 4.4. True for `n <= 2`
(`fp-groups-have-simply-connected-rips-complexes`).

## Attempts

- Brown's criterion for filtrations gives only essential connectivity: each
  sphere in `R_t` dies in some `R_{t'}`, but `R_{t'}` has new spheres. Pushing
  every sphere back to scale `t` is exactly what is missing.
- Push-down deformations (Rips's argument for hyperbolic groups, discrete
  Morse theory on word length as in Zaremsky arXiv:1812.10976) need a
  combing-type geometric input that type `F_n` does not provide. Dies for
  general groups.
- Flag models with one vertex orbit. A finite K(G,1) n-skeleton gives a free
  cocompact (n−1)-connected flag complex (after barycentric subdivision) with
  several vertex orbits. Contracting an equivariant matching of edges between
  two orbits preserves homotopy type when the link condition holds, and every
  edge of a flag complex satisfies it. But after contraction the complex need
  not be flag, and replacing it by the clique complex of its 1-skeleton can
  change the homotopy type. Open.
- Special classes, established 2026-09-13:
  - direct products of positive cases
    (`connected-rips-complexes-pass-to-direct-products`);
  - groups acting freely and transitively on the vertices of an
    (n−1)-connected level set of a CAT(0) cube complex
    (`cube-level-set-clique-complexes-model-the-level-set`);
  - every Bestvina–Brady group of type `F_n`
    (`bestvina-brady-groups-have-connected-rips-complexes`).
  The cube method never reaches infinite Kazhdan groups of type `F_n` (e.g.
  `SL_3(Z)`), since (T) groups have a global fixed point on CAT(0) cube
  complexes and so cannot act freely on vertices.
