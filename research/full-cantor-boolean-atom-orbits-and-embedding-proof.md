---
rg: 2
id: full-cantor-boolean-atom-orbits-and-embedding-proof
kind: route
title: Classify clopen tuples by their nonempty Boolean atoms and apply the type A criterion
target: fp-full-binary-cantor-groups-have-type-a-actions
requires:
  - full-binary-cantor-groups-have-copy-stabilizers
  - type-a-action-gives-boone-higman-for-subgroups
artifacts:
  - research/artifacts/boone-higman-full-cantor-clopen-action-2026-09-08.md
---

Every clopen subset of C is a finite union of binary cones, so
there are countably many. If a homeomorphism fixes every proper
nonempty clopen set setwise, clopen separation of distinct points
forces it to fix every point. Thus the action is faithful.

For a tuple of n clopen sets, label its Boolean atoms by binary
membership vectors in {0,1}^n. Two tuples are in the same V orbit
exactly when the same labeled atoms are nonempty. For sufficiency,
write corresponding nonempty atoms as finite unions of cones,
refine their binary leaf counts to agree, and match the leaves
on each labeled atom. The resulting global prefix map belongs to V.
Necessity holds for every homeomorphism. Consequently adjoining
more homeomorphisms cannot merge these patterns, and D has
finitely many tuple orbits of every length.

For two proper nonempty clopen sets U,W, their four atoms form
a binary two-by-two support matrix. Neither row nor column may
be empty. There are two patterns with two nonempty atoms
(equality and complementarity), four with three nonempty atoms,
and one with all four nonempty. Each pattern is realized by
partitioning C into that many cones. This gives exactly seven
ordered-pair orbits.

Removing equality and forgetting the order identifies the two
proper-containment orientations and leaves the other patterns
unchanged. There are exactly five orbits of two-element subsets:
complementary, disjoint with nonempty complement, overlapping
with union C, properly nested, and overlapping with nonempty
complement of their union.

The required copy-stabilizer theorem makes a point stabilizer
D times D, hence finitely presented and finitely generated.
The actor D is finitely presented by hypothesis. This verifies
every condition of type (A), and the required embedding theorem
gives a finitely presented simple overgroup of D.

The notion of full used here agrees with Definition 2.24 of
[Belk--Bleak--Matucci--Zaremsky](https://arxiv.org/pdf/2309.06224).
The final embedding uses [Zaremsky's type (A) criterion](https://arxiv.org/pdf/2405.18354).
The clopen action and its direct-product stabilizers avoid any
assumption about the stabilizers of individual Cantor points.
