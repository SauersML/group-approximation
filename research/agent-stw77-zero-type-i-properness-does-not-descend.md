---
rg: 2
id: agent-stw77-zero-type-i-properness-does-not-descend
kind: claim
title: Type-I properness does not descend even at zero Kadison--Kastler distance
distinct_from:
  agent-stw77-zero-packetwise-type-i-descent-fails: that shows an absorbed finite-dimensional algebra can stay far from the represented target; this places the algebra exactly inside the represented target and shows that its proper-support property still does not descend.
  agent-stw77-zero-type-i-weak-closure-obstruction: that changes von Neumann type or loses properness after shrinking the ambient algebra; this uses a faithful essential type-I representation throughout.
---

There are a separable unital properly infinite C-star algebra `B`, a faithful
essential representation `pi:B->B(H)`, and a unital finite-dimensional
subalgebra `D subset B` such that every minimal projection of `pi(D)` is
properly infinite in `B(H)`, while one minimal projection of `D` is finite in
`B`.

Moreover the scalar map `phi:C->B` has nuclear dimension zero and satisfies
the proper-image hypothesis, and

```text
(pi compose phi)(C) subset pi(D) subset pi(B).
```

Thus the finite-dimensional represented model has zero range-approximation
error and zero Kadison--Kastler descent error.  Nevertheless its
proper-support conclusion does not return to `B`.

Consequently an operator-norm descent principle for the finite-dimensional
algebra alone cannot prove `stw77-zero-models-admit-proper-block-clustering`.
A successful use of the type-I theorem must also descend Cuntz comparison or
the two corner isometries witnessing proper infiniteness; faithful essential
representation and arbitrarily strong norm control on the model algebra do
not reflect that property.
