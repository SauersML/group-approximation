---
rg: 2
id: virtually-free-reflections-share-all-residuals-proof
kind: route
title: Intersect the common factorization kernels and test property T on the visible quotient
target: virtually-free-reflections-share-all-residuals
requires:
  - leavitt-unit-internal-all-virtually-free-reflections
---

Every homomorphism from `W_Q` to an MF, finite, compact, finite-dimensional
unitary, or finite-dimensional linear target kills every coordinate copy of
`U`.  It therefore kills `B_Q` and factors uniquely through `Q`.

Conversely, `Q` is residually finite.  Given `1!=q in Q`, choose a finite
quotient detecting it.  That quotient is itself an MF and compact target.  It
also embeds by its regular permutation representation into a unitary group,
and into `GL_n(k)` over every field `k`: distinct permutations give distinct
permutation matrices in every characteristic.  Thus every element outside
`B_Q` is detected by each target class in `(UVR1)`.  This proves all the
residual equalities.

The factorization bijections into finite groups are precisely the universal
property determining profinite completion, and those into compact groups are
the universal property determining Bohr compactification.  They give the
canonical isomorphisms `(UVR2)`.  The dimension-by-dimension factorization
gives the remaining representation-functor statement.

Suppose now that `Q` is finitely generated.  If `Q` is finite, then `B_Q` is
a finite direct product of copies of the Kazhdan group `U`; it has property
`(T)`.  The group `W_Q` is a finite extension of `B_Q`, so it also has
property `(T)`.

If `Q` is infinite, it has a finite-index free subgroup of positive rank.
Such a free group does not have property `(T)`, and property `(T)` passes to
finite-index subgroups.  Hence `Q` does not have property `(T)`.  Since `Q`
is a quotient of `W_Q` and property `(T)` passes to quotients, `W_Q` cannot
have property `(T)`.  This proves `(UVR3)`.
