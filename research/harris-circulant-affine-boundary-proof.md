---
rg: 2
id: harris-circulant-affine-boundary-proof
kind: route
title: Classify translation-invariant color-equality graphs as subgroup-coset bicliques
target: harris-circulant-one-matrix-compiler-forces-affine-support
requires:
  - harris-bisynchronous-game-algebra-preservation
  - monomial-game-pair-compatibility-is-projective-color-rigid
---

Equality of a source color and a target color partitions the bipartite graph
into complete bipartite components.  For the Cayley relation
`i~a iff a-i in R`, every element of `R-R` lies in the same left component as
zero and consequently stabilizes `R` by translation.  The stabilizer is
therefore `R-R`, a subgroup, and `R` is one of its cosets.  Cosets give the
converse by quotient coloring.  Harris's formula `(HCM3)` turns a fixed
question-pair support into exactly this Cayley relation on `A x A`.
