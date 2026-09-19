---
rg: 2
id: stw59-joined-base-independent-euler-coordinates-proof
kind: route
title: Equal-dimension joined bases have independent Euler coordinates preserved by the simple twisted tower
target: stw59-exact-finite-abelian-unitary-component-groups
requires:
  - stw59-exact-arbitrary-cyclic-unitary-component-groups
artifacts:
  - research/artifacts/stw59-exact-finite-abelian-component-groups-2026-09-05.md
---

For G=direct-sum Z/d_alpha choose R=max d_alpha. The alpha-th arm
is S2 times CP^(d_alpha-1) times CP^(R-d_alpha), carrying the rank-R
bundle C^(d_alpha) plus R-d_alpha tautological lines. Join the arms
at chosen points and glue their fibers, preserving a trivial rank-two
summand.

At every stage the gauge/section exact sequence computes the whole
component group as top cohomology modulo the integral Euler image.
Top cohomology has one independent coordinate per arm. Restriction
forces divisibility by d_alpha in that coordinate. The reduced S2
Bott class times the distinguished projective line extends by zero
over the other arms and attains exactly plus or minus d_alpha in
only that coordinate. Hence the image is precisely the direct sum
of the d_alpha integer lattices, without hidden coupling relations.

Adding a tautological block over CP^r multiplies every top obstruction
coordinate by its top Chern number, plus or minus one. Evaluation
blocks contract for each fixed unitary, so the actual connecting maps
induce group isomorphisms. Dense-tail evaluations give a simple AH
limit, compatible faithful traces give stable finiteness, and even
cells give K1 zero. Polar approximation and finite-stage path
detection identify its entire component group with G.
