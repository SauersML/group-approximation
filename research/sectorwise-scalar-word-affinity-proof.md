---
rg: 2
id: sectorwise-scalar-word-affinity-proof
kind: route
title: Compare group-basis support after projecting to the negative selector sector
target: sectorwise-scalar-finite-group-words-are-selector-affine
requires: []
---

Centrality of `D` decomposes the marked finite group algebra as the direct sum
of its `p_chi` blocks.  A word which is the same scalar on every simple block
above `chi` equals that scalar times the block identity, so summing over
marked `chi` gives `(SSW4)`.  Expanding `p_-=(1-J)/2` gives `(SSW5)`.

The elements of a finite group are a basis of its complex group algebra.  If
`w` is outside `D`, then so is `Jw`, and they are distinct because `J` is a
nontrivial involution.  Their nonzero coefficients in `(SSW5)` cannot be
matched by an element supported on `D`.  Therefore `w` lies in `D`, where its
evaluation is a linear character and hence an affine Boolean phase.

