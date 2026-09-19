---
rg: 2
id: binary-schur-head-inner-holonomy-proof
kind: route
title: Project to the two child summands and apply Skolem-Noether
target: binary-schur-head-embeddings-are-relative-inner-holonomies
requires: []
---

Let `pr_+` and `pr_-` be the two coordinate maps from
`M_n(k) direct_sum M_n(k)`.  If `psi` is unital, both
`pr_epsilon after psi` are unital homomorphisms `M_n(k)->M_n(k)`.  Their
kernels are two-sided ideals and cannot be all of `M_n(k)`, so simplicity
makes both maps injective.  Equal finite dimension makes them automorphisms.
Skolem--Noether supplies `u_epsilon in GL_n(k)` and gives `(BRH3)`.

Changing the source frame multiplies both `u_epsilon` on the right and hence
conjugates `u_-^-1u_+`; a common target head-frame change multiplies both on
the left and cancels from the relative element.  Independent target branch
changes do not preserve it; in a network they are precisely the endpoint
gauges, whose contributions cancel only around a closed cycle.  After fixing
the packet's two target frames, the remaining transition is represented by
`u_-^-1u_+`, with scalar multiples acting trivially.  This gives `(BRH4)`.
The `m`-branch statement is the same argument after all `m` coordinate
projections.
