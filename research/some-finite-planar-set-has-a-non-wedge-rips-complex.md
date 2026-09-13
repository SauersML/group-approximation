---
rg: 2
id: some-finite-planar-set-has-a-non-wedge-rips-complex
kind: claim
title: "Some finite planar set has a connected Rips complex that is not homotopy equivalent to a wedge of spheres"
distinct_from:
  some-infinite-planar-set-has-a-non-wedge-rips-complex: this claim asks for a finite point set; that claim asks for an infinite one
artifacts:
  - research/artifacts/zp-planar-rips-search-2026-09-13.md
---

There are a finite set `X ⊆ R^2` (Euclidean metric) and a scale `r > 0` such
that `R_r(X)` is connected and not homotopy equivalent to any wedge of
spheres. This is the negation of
`rips-complexes-of-finite-planar-sets-are-wedges-of-spheres`.

A finite example also gives an infinite one: add infinitely many points within
distance `ε` of one point `x_0 ∈ X`, where `ε` is smaller than every gap
`|d(x,y) − r|` over pairs in `X`. Each new point is then adjacent to exactly
the neighbours of `x_0`, and the simplicial retraction sending the new points
to `x_0` is contiguous to the identity, so the Rips complex keeps its
homotopy type.

**Constraints any example must meet.** `π_1` is free
(`planar-rips-projection-is-a-pi1-isomorphism`), and induced normal
pseudomanifolds of dimension `≥ 2` are crosspolytope boundaries
(`planar-rips-pseudomanifolds-are-crosspolytope-boundaries`). So a
counterexample needs torsion in homology, twisted structure over its free
fundamental group, or non-trivial attaching between spheres (e.g. a cup
product or a Hopf-type cell).

## Attempts

- **(A) Torsion.** Homology torsion rules out a wedge at once. Bounded search
  over 14 families (random clouds, noisy circles, Reuleaux polygons,
  concentric polygons, lattice annuli, rings of polygons), about 24,000
  reduced complexes: no torsion mod 2 or mod 3
  (`research/artifacts/zp-planar-rips-search-2026-09-13.md`).
- **(B) A circle of spheres around a hole.** Place finite clusters around a
  large circle, symmetric under a rotation of order `N`, with clusters more
  than `r` apart unless they are neighbours. Van Kampen gives `π_1 = Z` when
  the pairwise unions have simply connected Rips complexes. By
  `wedges-of-spheres-have-free-cyclic-cover-homology`, a wedge would make the
  homology of the infinite cyclic cover free over `Z[t^{±1}]` in degrees
  `≥ 2`. If each cluster carries an octahedral `S^2` and in the union of two
  neighbours both spheres are nonzero multiples `a, b` of one generator of
  `H_2 = Z`, then Mayer–Vietoris gives `H_2(cover) = Z[s^{±1}]/(a − bs)`, with
  `s` the one-step rotation and `t = s^N`. That module is not free, so
  `R_r(X)` would not be a wedge. Obstacle: carrying a sphere from one cluster
  to the next needs vertex exchanges over distances below `r`, while
  separation needs steps above `r`. In the search, separated clusters gave
  independent spheres (`S^1 ∨ ⋁ S^2`), and dense sliding (the `tracks` and
  `squash` families) collapsed every local sphere, leaving `S^1`.
- **(C) Winding certificate at any hole.** For every point `p` outside the
  shadow, the angle around `p` gives an infinite cyclic cover; a discrepancy
  between twisted and ordinary Betti numbers in degree `≥ 2` certifies a
  non-wedge. Tested on every core with a hole in the search: no discrepancy.
- **(D) Structure of cores.** Near the diameter scale, reduced cores almost
  always have far graphs (pairs at distance `> r`) that are disjoint unions of
  cycles and edges. Their Rips complexes are then joins of `S^0`s and of
  independence complexes of cycles, hence wedges. The rare cubic far graphs
  (12 vertices, `S^2 ∨ S^2 ∨ S^2`) are being classified. A structure theorem
  for cores would point to a positive answer.
