---
rg: 2
id: planar-polyhedron-inclusions-have-free-factor-pi1-images
kind: claim
title: "An inclusion of compact connected planar polyhedra maps the fundamental group onto a free factor"
distinct_from:
  planar-rips-projection-is-a-pi1-isomorphism: that claim identifies the fundamental group of one finite planar Rips complex with that of its shadow; this one compares two nested shadows and says how the smaller group sits in the larger
  planar-rips-complexes-have-free-first-homology: that claim is about first homology, where the inclusion maps are read off winding numbers; this one is the nonabelian statement, which winding numbers do not see
---

Let `K ⊆ L ⊆ R^2` be compact connected polyhedra (finite unions of points,
segments and triangles) and `x_0 ∈ K`. Then the image of

`i_* : π_1(K, x_0) → π_1(L, x_0)`

is a free factor of the free group `π_1(L, x_0)`.

**Why it matters.** Purely algebraically, a composite of "kill some
generators, then include as a free factor" steps need not have free-factor
image (`x_1^2 x_n` is primitive in `F(x_1, x_n)`, but killing `x_n` leaves
`x_1^2`). This was recorded as the place where freeness of `π_1` for infinite
planar Rips complexes died
(`research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md`, §6).
The claim applies the planar picture to `K ⊆ L` directly, never to a composite,
and so avoids that example. Its main use is
`planar-rips-pi1-is-aleph1-free-and-free-when-countable`.

**Shape of the proof.** Replace `K ⊆ L` by nested regular neighbourhoods
`M ⊆ int M'`, compact planar surfaces. Cut `M'` along the boundary circles of
`M`. Each piece outside `M` is either a disk filling a hole of `M`, which kills
one basis element, or a planar surface in which the gluing circle is
primitive, which adds a free factor. Proof in
`planar-polyhedron-inclusions-have-free-factor-pi1-images-proof`.

## Attempts

- 2026-09-18 (swarm-0917-w10-w10-z-break): proved by the regular-neighbourhood
  cut-and-paste argument in the companion route. Only textbook PL topology
  (regular neighbourhoods, collars, Schoenflies), van Kampen and bases of
  free groups of planar surfaces are used.
