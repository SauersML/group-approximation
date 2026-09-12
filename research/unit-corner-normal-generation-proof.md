---
rg: 2
id: unit-corner-normal-generation-proof
kind: route
title: Corner elimination writes every unit of the kernel inside a proper matrix corner
target: unit-corner-embedding-normally-generates-commutators
requires:
  - agp-purely-infinite-simple-k1-is-unit-abelianization
  - full-idempotent-ring-has-properly-infinite-unit
artifacts:
  - research/artifacts/k1-classification-and-extension-bridge-2026-09-07.md
---

## Why sufficient

Write `N` for the normal closure and `kappa : R^x -> K_1(R)` for the natural
map, whose kernel is `[R^x,R^x]` by the first prerequisite.

**Containment.**  `EL_4(R)` is perfect, by the Steinberg relation
`e_(ij)(a) = [e_(ik)(a), e_(kj)(1)]` available in rank four, so
`jmath(EL_4(R))` consists of products of commutators of units and lies in the
normal subgroup `[R^x,R^x]`.  So `N <= [R^x,R^x]`.

**The reverse.**  Two constructions inside the proof of Ara--Goodearl--Pardo
Theorem 2.4 supply, for a purely infinite simple ring: every unit is
congruent modulo the commutator subgroup to one of the form
`v = e + (1-e)v(1-e)` with `e` a nonzero idempotent; and such a supported
unit is represented by `diag(v,1,...,1)` inside a proper matrix corner built
from orthogonal idempotents each equivalent to `1`.  When `kappa(v) = 0` the
stabilization may be taken elementary.

Each elementary generator of that stabilization lies in a four-coordinate
elementary subgroup, so it lies in a corner copy of `EL_4(R)` with nonzero
complement.  Two such corners have complements with equal `K_0` class and
both nonzero, so by Ara--Goodearl--Pardo Proposition 2.2, quoted, "any nonzero
finitely generated projective `R`-modules which are stably isomorphic must be
isomorphic", the complements are isomorphic and the corners are conjugate by
a unit of `R`.  So each such generator lies in `N`, and therefore
`v in N`.  Since every element of `ker kappa = [R^x,R^x]` is a product of
such supported units modulo the commutator subgroup, `[R^x,R^x] <= N`.

**Trust boundary.**  Proposition 2.2 and Corollary 1.7 of that paper were read
verbatim; the two constructions inside the proof of Theorem 2.4 were read in
summary.
