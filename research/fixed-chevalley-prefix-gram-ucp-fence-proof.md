---
rg: 2
id: fixed-chevalley-prefix-gram-ucp-fence-proof
kind: route
title: Linearize bounded root-word derivations and separate tracial positivity from exact labelled positivity
target: fixed-chevalley-prefix-grams-give-only-tracial-positivity
requires: []
artifacts:
  - research/artifacts/fixed-chevalley-prefix-gram-ucp-fence-2026-08-21.md
---

For a fixed root-word atlas choose one unitary product `V_i=U_n(p_i)` at
each vertex.  Then `[V_i^*V_j]` is a Gram matrix and hence positive.  If two
labelled edges represent the same group word by a derivation using `N`
conjugates of presentation relators, unitary invariance and telescoping bound
the normalized Hilbert--Schmidt difference of their entries by the sum of
those `N` relator defects.  Applying this to the fixed quarter-turn and braid
derivations proves distance `o(1)` from the affine repeated-label space.

Exact complete positivity requires positivity after the repeated entries
have been made literally equal.  Orthogonal affine projection need not
preserve the positive cone, while positive-part truncation need not preserve
the affine equalities.  Root-subgroup averaging does not remove this
intersection problem: invariance under every root subgroup is invariance
under their generated group and is equivalent to the desired globally
positive-definite kernel.  No such simultaneous correction follows from the
word telescoping calculation.

For the stronger fixed-level statement, define the unital star-linear
coordinate map on the finite generator system by sending each canonical
root unitary to its chosen matrix representative.  At every fixed matrix
level, the image of a positive element is positive in the tracial quotient,
so the normalized Hilbert--Schmidt norm of its negative part tends to zero.
Compactness of the positive unit ball at that fixed level and uniform
boundedness of the coordinate maps make the convergence uniform there.
Smith's criterion tests maps into `M_(d_n)` at level `d_n`, so this fixed-level
fact does not imply complete positivity; a surviving witness must move to
unbounded amplification level.
