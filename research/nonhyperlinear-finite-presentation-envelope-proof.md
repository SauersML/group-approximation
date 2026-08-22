---
rg: 2
id: nonhyperlinear-finite-presentation-envelope-proof
kind: route
title: Present a forbidden finite multiplication window by its partial table
target: nonhyperlinearity-has-a-finite-presentation-envelope
requires: []
---

Negate the finite-window criterion for `G` and choose a bad finite window
`F`.  The presentation `(FPE1)` has finitely many generators and relators.
The evaluation map to `G` proves that no two distinct names collapse in the
presented group.

If that group were hyperlinear, request a microstate on the finite set of all
names, all products occurring in `(FPE1)`, and all differences
`x_g^(-1)x_h` for `g != h`.  Multiplicativity transfers every visible product
of `F`, while canonical trace separation of the nonidentity differences
transfers pairwise normalized-HS separation.  Taking the error below the bad
window threshold contradicts its definition.
