---
rg: 2
id: mixed-central-cnot-completes-relative-rank-one-router-proof
kind: route
title: Solve two invariant quadratic forms with a prescribed flag transvection
target: mixed-central-cnot-completes-relative-rank-one-router
requires:
  - predicate-activated-cnot-routes-relative-pauli-halves
  - central-packet-sign-supplies-marked-carrier
artifacts:
  - experiments/mixed_commutator_cnot_completion.py
---

Index the 15 upper-triangular commutators of six involutions.  The `K` and `J`
coefficient vectors of `(MCR1)` are

```text
K=(1,0,1,0,1,1,0,0,0,0,0,1,0,1,0),
J=(0,0,1,0,0,0,0,0,0,1,0,0,0,0,0).
```

The verifier checks that the six columns in `(MCR2)` are linearly independent,
preserve both alternating forms, and have zero square in both central labels.
The last check is essential in characteristic two: an earlier alternating-
form solution sent one involution to a word whose square was `K` and was
correctly rejected.

Gaussian elimination of the two evaluated alternating forms gives `(MCR3)`.
The entries `(0,1)` and `(2,3)` of the two symbolic forms are respectively
`K` and `J`, while entry `(0,3)` is `KJ`; this is exactly `(MCR4)`.
The image column of `g_1` is fixed and that of `g_3` is `g_1g_3`, proving the
flag routing statement.

For comparison, the verifier exhausts the block-diagonal packet with planes
labelled `K,J,KJ` and finds no completion.  There `d` lies in the radical of
the `K` form but `bd` does not, contradicting radical preservation.  The
cross commutators in `(MCR1)`, rather than an additional disjoint tensor
factor, are what remove this obstruction.  All reported positive identities
are exact certificate checks; the retained matrix is hard-coded after search.
