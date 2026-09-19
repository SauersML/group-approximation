---
rg: 2
id: odd-leavitt-reflection-matrix-calculation-proof
kind: route
title: Multiply the signed partial swaps and invoke the p-uniform Heisenberg packet
target: odd-leavitt-steinberg-reflection-prerequisites
requires:
  - leavitt-prefixes-form-exponential-heisenberg-packet
  - leavitt-steinberg-quadratic-radius-pressure
---

The finite-presentation statement is the rank-`r>=4` Krstic--McCool theorem
already source-pinned in `atlas-relator-extraction-2026-08-15`.  Expanding
the standard Weyl word `(OLR4)` gives `(OLR5)`.

Under `(OLR6)`, direct multiplication of the three elementary matrices in
`(OLR7)` gives `(OLR8)`.  Multiplication by its displayed inverse shows that
it conjugates `qE_bb` to `pE_aa`.  The two factors in `(OLR9)` have disjoint
indices, so applying this twice conjugates
`q(E_33+E_44)` to `p(E_11+E_22)`, which is `(OLR10)` after replacing a
projection `e` by `u_e=1-2e`.

The two Steinberg words in `(OLR10)` have the same elementary image, so their
quotient belongs to the stable central kernel; no defining Steinberg
relation cited here identifies that quotient with one.  Finally the existing
Heisenberg packet theorem gives `(OLR12)` for arbitrary prime `p`, proving
the finite-dimensional annihilation statement without a second construction.

