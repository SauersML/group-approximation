---
rg: 2
id: fixed-rank-index-authenticator-has-gap-or-functoriality-proof
kind: route
title: Apply rank-nullity and the spectral gap dichotomy to a fixed decoded block
target: fixed-rank-index-authenticator-has-gap-or-functoriality
requires: []
---

For `A:PH->QH`, rank-nullity subtracts the same `rank(A)` from the
dimensions of `PH` and `QH`, proving `(FRI2)--(FRI3)`.  The pair
`0, epsilon I_d` proves `(FRI4)` in every dimension.

If `spec(A^*A)` avoids `(0,gamma)`, choose continuous `f` equal to one at
zero and zero on `[gamma,1]`.  Then `f(A^*A)` is exactly the kernel
projection.  Continuous functional calculus and trace exist unchanged in
every finite tracial von Neumann algebra, and uniform polynomial
approximation supplies the claimed moment modulus.  The same proof applies
to any hard spectral threshold separated by an empty band.

Finally `(FRI7)` is a direct scalar calculation.  Without a lower spectral
bound, `epsilon I_d,epsilon^2 I_d` prove discontinuity of normalized log
determinant; with `A^*A>=gamma I`, continuous functional calculus gives
`(FRI8)`.  These alternatives exhaust the fixed hard-rank and determinant
readouts asserted in the claim.
