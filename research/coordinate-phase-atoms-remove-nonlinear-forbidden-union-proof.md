---
rg: 2
id: coordinate-phase-atoms-remove-nonlinear-forbidden-union-proof
kind: route
title: Refine the forbidden carrier by joint spectrum and expand coordinate covariance
target: coordinate-phase-atoms-remove-nonlinear-forbidden-union
requires: []
---

The joint functional calculus of commuting involutions gives the PVM
`(P_a)`.  Since every type projection commutes with that PVM, the projections
`P_aQ_lambda` are orthogonal in `a` and `lambda`.  Replacing each finite rank
by its largest multiple of four loses at most three dimensions, proving
`(CPA3)` after summing the fixed menu.

For `(CPA4)`, insert `sum_aP_a=1` on the left and `sum_bQ_b=1` on the right.
The blocks `P_a(Z_iU-UW_i)Q_b` are mutually Hilbert--Schmidt orthogonal and
equal `(a_i-b_i)P_aUQ_b`.  Squaring and summing first in `(a,b)` and then in
`i` gives the coefficient `4 Ham(a,b)`.  Every off-diagonal pair has Hamming
distance at least one, which proves `(CPA5)`.

