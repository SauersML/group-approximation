---
rg: 2
id: derived-reset-source-deficit-proof
kind: route
title: Rank-nullity gives a half-carrier source-Gram floor
target: derived-reset-packets-do-not-saturate-both-children
requires: []
---

The positive contraction `S^*S` has rank at most the child rank `n`.  On the
`2n`-dimensional range of `P`, at least `n` eigenvalues are therefore zero.
On each corresponding vector `(S^*S-P)^2` has eigenvalue one.  Dividing by
`2n` proves the half-rank floor; multiplying by the ambient carrier mass gives
`tau(P)/2`.

In the exact Pauli transfer packet the two source Grams have trace `1/8` and
their orthogonal ranges sum to a carrier of trace `1/4`.  Thus the branch is
stationary at the smaller source scale, while any return of the doubled target
to that same source would be a forbidden proper-corner return.  This is the
claimed obstruction.
