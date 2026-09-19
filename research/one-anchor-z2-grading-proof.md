---
rg: 2
id: one-anchor-z2-grading-proof
kind: route
title: Expand in the anchor grading and use the reflection square identity
target: one-anchor-grading-makes-parity-damage-quadratic
requires: []
---

The two eigenspaces of `Ad(A)` are orthogonal and multiply according to the
`Z2` grading.  Expanding a word in its even and odd factors therefore makes
`Phi_A` retain exactly the even-cardinality terms, proving `(OAG3)`.  Every
nonempty retained error term has at least two odd factors; put one in
operator norm, one in `L_2`, and bound all remaining contractions by one to
obtain `(OAG4)`.

Taking even and odd parts of `B_i^2=1` proves `(OAG2)`.  Taking the even
part of the commutator expansion proves `(OAG5)`.  Since `Y_i^2=1-X_i^2`
is a function of `X_i^2`, scalar functional calculus gives `(OAG6)` and
the operator-small hypothesis gives `(OAG7)`.
