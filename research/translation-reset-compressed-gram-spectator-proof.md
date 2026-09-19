---
rg: 2
id: translation-reset-compressed-gram-spectator-proof
kind: route
title: Compress the Gram spectator along the translation reset
target: translation-reset-leaves-a-compressed-gram-spectator
requires:
  - symmetrized-reset-collapses-schur-flow-to-one-ray
  - fanizza-compressed-unitary-has-guarded-rank-floor
  - diagonal-difference-shift-propagates-pauli-incidence
  - semisimple-trace-charts-cannot-authenticate-proper-fullness
---

Amplify one exact reset label representation by `C^N`.  With the notation
of `(RGS1)--(RGS2)`, choose `rank(Q)=sN/r`; then

```text
rank(E-q)=rN-sN=(r-s)N=rank(F).
```

Two equal-dimensional subspaces of a finite-dimensional Hilbert space are
carried to each other by a unitary (indeed by a symmetry).  Choose such a
`U` from `Ran(E-q)` to `Ran(F)` and extend it on the orthogonal complements.
Then `FUE` is isometric exactly on `Ran(E-q)` and vanishes on `Ran(q)`,
which proves `(RGS4)`.

The reset acts as `rho tensor I_N`, so all of its relations and its unique
type ray are unchanged.  A non-scalar `Q` puts `q` outside the represented
finite label algebra.  Tensoring an independent old-spin factor and using
`(RGS5)` verifies every diagonal-difference incidence.  Therefore neither
the reset nor Pauli localization supplies the algebra-coordinate hypothesis
needed by the semisimple trace gap.
