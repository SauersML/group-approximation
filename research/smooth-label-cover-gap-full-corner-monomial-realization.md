---
rg: 2
id: smooth-label-cover-gap-full-corner-monomial-realization
kind: claim
title: Complete the separated smooth-label-cover game to a full-corner finite-phase monomial matrix pair
distinct_from:
  smooth-label-cover-edges-are-finite-phase-projective-color: that solves every edge predicate independently; this must impose all edge tables together with square row and column relations and preserve the whole separated algebra.
  bisynchronous-to-monomial-game-algebra-compiler: that asks for a compiler for the Harris image of a general non-CE game; this starts from the narrower projective-color smooth-label source.
  monomial-gap-phase-safe-toric-groupification: that starts after a separated monomial linking algebra has already been constructed; this is the preceding global completion gate.
artifacts:
  - research/artifacts/cmps-smooth-label-monomial-audit-2026-08-23.md
---

**OPEN.**  For one `S_(loop,s)` from
`lin-gap-smooth-label-cover-projective-color-game`, construct a finite phase
order `r` and finite matrices `A,B` such that the `r`-monomial
quantum-isomorphism algebra `A_r(A,B)` is *-isomorphic to the synchronous
game algebra of `S_(loop,s)`, or contains it as an explicit full corner with
maps preserving both

```text
nonzero tracial representations, and
nonzero homomorphisms into R^omega.                      (SFM1)
```

The edge relations already have the required projective-color biclique form,
and `(LSG2)` even gives joint PVMs for every sampled edge in the chosen
perfect trace.  The missing work is global: smooth-label PVMs provide a row
partition for each question but not the column partitions of one square
quantum-reflection matrix, and the projection maps depend on the edge.  Any
auxiliary completion must be proved full; merely extending the perfect trace
can introduce an unrelated `R^omega` representation and destroy the
separation.

Harris's canonical circulant completion does not automatically solve this
special case.  After that completion a fixed accepted label support appears
as a translation-invariant Cayley relation.  By
`harris-circulant-one-matrix-compiler-forces-affine-support`, direct scalar
coloring works only when that support is a subgroup coset.  The CMPS labels
are satisfying-assignment tuples and their projection-fiber unions need not
be affine cosets.  A positive construction therefore needs a non-circulant
completion or genuine incidence/full-corner auxiliaries.
