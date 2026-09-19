---
rg: 2
id: fixed-finite-core-completion-proof
kind: route
title: Separate the compact zero-set branch from a regular-representation complement
target: fixed-finite-core-face-has-energy-paid-completion
requires: []
---

Continuity on the compact group `U(d)` proves `(FFC2)` exactly as follows:
define `f_sigma(t)` as the supremal distance to `Z_sigma` among points of
energy at most `t`; any failure of convergence to zero has a subsequence
converging to a point of `Z_sigma`.  If the zero set is empty, compactness
instead proves `(FFC3)`.

The restriction of the left regular representation is
`res_H^G(lambda_G)=[G:H]lambda_H`.  Every finite-dimensional `H`
representation occurs in a sufficiently large multiple of `lambda_H`, so
some `M` makes `(FFC4)` contain `sigma`.  Taking the orthogonal complement
gives `tau`, and pulling `M lambda_G` back along `q` gives the exact endpoint.
Equation `(FFC5)` follows from `(FFC3)`.

For a block-diagonal sum, empty-zero-set blocks have number at most total
energy divided by the minimum of their finitely many `delta_sigma`; changing
and padding them costs normalized Frobenius size proportional to the square
root of their relative count.  On nonempty-zero-set blocks, split at an
energy threshold and use `(FFC2)` below it and bounded unitary diameter above
it.  This proves the direct-sum assertion.
