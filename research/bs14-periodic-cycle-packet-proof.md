---
rg: 2
id: bs14-periodic-cycle-packet-proof
kind: route
title: Invariance of a finite weighted spectrum forces cycles and equal multiplicities
target: bs14-unitary-representations-are-periodic-cycle-packets
requires: []
---

Conjugacy in `(BP1)` says that `S` and `S^4` have the same eigenvalue
multiset.  Equivalently the positive integer weight function `m` on the
finite spectrum satisfies `m=p_*m` for `p(z)=z^4`.  In a finite directed
functional graph, a positive invariant weight cannot occur on a proper tree
feeding a cycle: a leaf has no incoming weight, and stripping leaves reaches
the cycle.  Hence every supported vertex lies on a cycle, `p` permutes the
support, and invariance makes the weights constant on each cycle.  Periodic
points of `z |-> z^4` satisfy `z^(4^m-1)=1`, hence have odd order.

The spectral projection relation obtained from `(BP1)` shows that `R`
unitarily transports the `j`-th eigenspace to the `(j-1)`-st eigenspace
around each cycle.  Choose bases successively so that all but the final
transport are the identity; their product around the cycle is one unitary
`V in U(k)`.  This gives `(BP3)--(BP4)`, and direct substitution proves the
converse.

Finally choose an orthonormal eigenbasis of the unitary `V` and use it on
every vertex of the cycle.  Since `S` is scalar on each vertex and all
non-return transports are identities, this decomposes `(BP3)--(BP4)` into
multiplicity-one invariant packets with scalar return phases equal to the
eigenvalues of `V`.
