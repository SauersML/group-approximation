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

Index the six upper-triangular commutators of four involutions in the order
`ab,ac,ad,bc,bd,cd`.  The `K` and `J`
coefficient vectors of `(MCR1)` are

```text
K=(1,0,1,1,0,0),
J=(0,0,1,0,0,1).
```

The verifier checks that the four columns in `(MCR2)` are linearly independent,
preserve both alternating forms, and have zero square in both central labels.
The last check is essential in characteristic two: an earlier alternating-
form solution sent one involution to a word whose square was `K` and was
correctly rejected.

Gaussian elimination of the two evaluated alternating forms gives `(MCR3)`.
The entries `(0,1)` and `(2,3)` of the two symbolic forms are respectively
`K` and `J`, while entry `(0,3)` is `KJ`; this is exactly `(MCR4)`.
The image column of `b` is fixed and that of `d` is `bd`, proving the
flag routing statement.

On `QF`, conjugation by `c` exchanges `D_+` and `D_-`.  Within either
`D_sigma` block, conjugation by `a` preserves `D_sigma` because
`[a,d]=KJ=+1` there, and exchanges `B_+` and `B_-` because
`[a,b]=K=-1`.  The four joint blocks therefore have equal trace, proving
`(MCR5)`.  Applying `phi(b)=b,phi(d)=bd` gives the stated sign map.

For comparison, the verifier exhausts all images of `a,c` in the uncoupled
four-generator packet with planes labelled `K,J`, while fixing
`b -> b,d -> bd`, and finds no completion.  There `d` lies in the radical of
the `K` form but `bd` does not.  The cross commutators in `(MCR1)` remove this
obstruction with no extra generators.  All identities are exact checks.
