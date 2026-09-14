---
rg: 2
id: leavitt-df-failure-by-single-shear-conjugation
kind: route
title: Compress a chart projective strictly below an equal-rank chart projective with one shear and one group element
target: leavitt-unit-group-algebra-not-directly-finite
requires: []
---

**Dead.** Invalidated by `one-sided-shear-conjugates-cannot-strictly-nest`.

The approach: take finite charts `K, K'` of `Q = L_(F_2)(1,2)^x` and idempotents
`P in F_2[K]`, `f in F_2[K']` of equal normalized rank, a group element `g`, and a
square-zero shear `N` from a single Peirce corner of `P`. The hope was a strict
nesting `W f W^-1 < P` with `W = (1+N)[g]`. Then `P` would be equivalent to a proper
subidempotent of itself, and padding gives a one-sided inverse pair.

The obstruction lemma shows that even one-sided nesting forces equal left, or
right, ideals, and two-sided nesting forces equality, whatever the support of
`N` and whatever `g`. It does not cover the two-shear architectures of the
prefix-corner shear note and of the half-corner artifact. Those use shears in
both Peirce orientations, and they produce corner pairs `B A = e` rather than a
conjugated subidempotent.

Recorded with `requires: []` only so the invalidation has a target; it asserts
nothing while its invalidator is established.
