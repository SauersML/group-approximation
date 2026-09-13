---
rg: 2
id: some-finite-planar-set-has-a-non-wedge-rips-complex
kind: claim
title: "Some finite planar set has a connected Rips complex that is not homotopy equivalent to a wedge of spheres"
distinct_from:
  some-infinite-planar-set-has-a-non-wedge-rips-complex: this claim asks for a finite point set; that claim asks for an infinite one
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

## Attempts

- **(A) Torsion.** Homology with torsion rules out a wedge at once. Plan: a
  bounded search over small planar configurations and scales, reducing each
  complex by dominated vertices (a vertex whose closed neighbourhood lies in
  another's can be deleted without changing the homotopy type) and comparing
  ranks of boundary maps over `F_2`, `F_3` and a large prime. Not yet run.
- **(B) A circle of spheres around a hole.** Place finite clusters
  `U_0, …, U_{N−1}` around a large circle, symmetric under a rotation of
  order `N`, with `d(U_i, U_j) > r` unless `j ∈ {i−1, i, i+1}` (mod `N`).
  Every simplex lies in some `K_i = R_r(U_i ∪ U_{i+1})`, and
  `K_i ∩ K_{i+1} = L_{i+1} = R_r(U_{i+1})`. If every `K_i` is simply connected
  and every `L_i` connected, van Kampen gives `π_1 = Z`. A wedge with
  `π_1 = Z` has the form `S^1 ∨ W`, whose universal cover has homology free
  over `Z[t^{±1}]` in each degree `≥ 2`. When `L_i ≃ S^2`, the Mayer–Vietoris
  sequence of the universal cover (an infinite chain of copies of `K_i`)
  gives `H_2 = coker(Z[s^{±1}] ⊗ H_2(L) → Z[s^{±1}] ⊗ H_2(K))`, where `s` is
  the one-step rotation and the deck generator is `t = s^N`. If
  `H_2(K) = Z` and the two cluster spheres map to `a` and `b` times its
  generator with `a, b ≠ 0`, the cokernel is `Z[s^{±1}]/(a − b s)`, which is
  not a free `Z[t^{±1}]`-module, so `R_r(X)` is not a wedge. Open design
  problem: clusters whose octahedral spheres (regular hexagons at scale just
  below their diameter give boundaries of octahedra) are both nonzero in
  `H_2(K)` while clusters two steps apart stay more than `r` apart. With
  translates of one hexagon this fails: carrying the sphere needs vertex
  exchanges over distances below `r`, while separation needs steps above `r`.
- **(C) Periodic strips.** Bend a translation-periodic strip configuration
  into an annulus with `N` periods and large radius, keeping all pairwise
  distances away from `r`, so the unit-distance graph is the quotient of the
  strip's. If the bent complexes `T_N` and `T_M` (`N ≠ M`) were both wedges,
  the strip complex's `H_2` would be free over `Z[s^{±N}]` and over
  `Z[s^{±M}]` with ranks `b_2(T_N)` and `b_2(T_M)`, forcing
  `M·b_2(T_N) = N·b_2(T_M)`. A strip with bounded nonzero `b_2(T_N)` would
  therefore give counterexamples. Candidate strips not yet chosen.
