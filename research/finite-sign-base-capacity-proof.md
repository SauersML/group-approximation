---
rg: 2
id: finite-sign-base-capacity-proof
kind: route
title: Bound the binary sign rank by the two finite coset counts
target: finite-sign-safe-base-has-bounded-pauli-capacity
requires: []
---

There is one row of `(FSB1)` for each X coset and one column for each Z
coset, giving `(FSB2)`.  Put the matrix into symplectic normal form.  A binary
commutation matrix of rank `r` has alternating completion
`[[0,M],[M^T,0]]` of rank `2r`, hence the standard finite Clifford
representation has dimension `2^r`.  This proves `(FSB3)`.

Repeating a row or column type adds multiplicity, not binary commutation rank.
Thus arbitrarily many local game occurrences can reuse this one fixed
representation and do not imply an unbounded local-dimension lower bound.
