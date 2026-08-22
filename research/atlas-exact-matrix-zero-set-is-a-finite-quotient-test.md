---
rg: 2
id: atlas-exact-matrix-zero-set-is-a-finite-quotient-test
kind: claim
title: The exact packet-collision matrix zero set is nonempty exactly when the quotient has a nontrivial finite quotient
distinct_from:
  atlas-a4-packet-collision-quotient-audit: that gives a conditional fork if the entire presented quotient is finite; this only asks for one exact finite-dimensional representation and converts its linear image to some nontrivial finite quotient.
  atlas-a4-root-ellipse-exact-tracial-escape: that constructs an exact solution in an arbitrary finite factor; Malcev separation applies to finite-dimensional linear images and does not apply to that diffuse factor model.
  atlas-a4-root-energy-ellipse-ceiling: that concerns approximate solutions in unbounded matrix dimensions; this identifies only the exact zero set at one finite dimension.
---

Put

```text
Gamma_A4=(A8*A8)/<<thirty packet words,q_19243>>.
```

The following are equivalent.

1. There is an exact finite-dimensional matrix model of the packet and
   collision relations in which both chart restrictions are faithful regular
   multiples of `A8`.
2. `Gamma_A4` has a nontrivial finite quotient.

Moreover, if either condition holds, there is an exact regular-margin matrix
model with root ellipse

```text
F>=1.                                                  (EXACT-MAT-FQ-1)
```

Indeed the model in `(EXACT-MAT-FQ-1)` may be taken to be the left regular
representation of the finite quotient.

Thus a low fixed-dimensional search cannot produce a new kind of exact
matrix-only point between the classical finite-quotient fence and the diffuse
finite-factor escape.  Any exact matrix point already forces a finite quotient
countermodel.  This does not address approximate solutions with dimensions
tending to infinity: the finite quotients supplied by Malcev need not be
uniform along such a sequence.

For clarity, the arbitrary-matrix lower inequality at the ellipse wall is
already established independently by
`atlas-root-energy-ellipse-controls-s3-distance`:

```text
F >= (3/4) max(0,(sqrt(2)-||q_19243(U)-1||_2)/8)^2.
```

At an exact collision solution this is `F>=3/128`.  The new content here is
the exact-zero-set/finite-quotient equivalence, not a duplicate SOS proof of
that lower bound.

