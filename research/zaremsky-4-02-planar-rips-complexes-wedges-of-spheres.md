---
rg: 2
id: zaremsky-4-02-planar-rips-complexes-wedges-of-spheres
kind: claim
title: "Zaremsky Problem 4.2 resolved: is every connected Rips complex of a (finite) planar set homotopy equivalent to a wedge of spheres?"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 4 (Vietoris–Rips
complexes), Problem 2, verbatim: "Is every (connected) Rips complex of every
(finite?) subset of the plane homotopy equivalent to a wedge of spheres?"

This claim is the question. It is established only through an answer route:

- **No, already for finite sets**: `zaremsky-4-02-by-no-finite` requires
  `some-finite-planar-set-has-a-non-wedge-rips-complex`.
- **Yes, for all subsets**: `zaremsky-4-02-by-yes-all` requires
  `rips-complexes-of-planar-sets-are-wedges-of-spheres`.
- **Yes for finite sets, no in general**: `zaremsky-4-02-by-split` requires
  `rips-complexes-of-finite-planar-sets-are-wedges-of-spheres` and
  `some-infinite-planar-set-has-a-non-wedge-rips-complex`.

Never write a `requires: []` route into this claim.

**Reading.**

- A subset `X ⊆ R^2` carries the Euclidean metric. For `r > 0` the Rips
  complex `R_r(X)` is the simplicial complex with vertex set `X` whose
  simplices are the finite subsets of diameter at most `r`, with the weak
  topology. It is the clique complex of the graph joining points at distance
  at most `r`. Rescaling gives `R_r(X) = R_1(X/r)`.
- For finite `X` the strict convention (diameter `< r`) produces the same
  family of complexes as `r` varies, so the finite reading does not depend on
  the convention. For infinite `X` both conventions are included.
- "Wedge of spheres" means `∨_{i∈I} S^{n_i}` with every `n_i ≥ 1`, any index
  set `I`, dimensions allowed to differ; the empty wedge is a point.
- "(finite?)" gives two readings, finite `X` and arbitrary `X`. Resolving the
  problem means deciding both; the three routes above cover every outcome.

**Partial results in the literature** (this lane verifies each statement from
the source before an import node lands; until then they are context only):

- Chambers, de Silva, Erickson and Ghrist (Discrete Comput. Geom. 44 (2010)):
  for finite planar `X`, the projection of `R_r(X)` onto its shadow in `R^2`
  induces an isomorphism on fundamental groups, so `π_1(R_r(X))` is free.
- Adamaszek (clique complexes of powers of cycle graphs) and Adamaszek–Adams
  (the Vietoris–Rips complexes of a circle, arXiv:1503.03669): Rips complexes
  of finite subsets of a circle, and of the circle, are homotopy equivalent to
  a point, an odd sphere, or a wedge of even spheres of one dimension.
- Adamaszek, Frick and Vakili, "On homotopy types of Euclidean Rips
  complexes" (arXiv:1602.04131, Discrete Comput. Geom. 58 (2017) 526–542).

## Attempts

- 2026-09-13 (z4-02-planar-rips): question and answer claims landed;
  literature verification in progress. The attacks on the negative side are
  recorded under `some-finite-planar-set-has-a-non-wedge-rips-complex`.
