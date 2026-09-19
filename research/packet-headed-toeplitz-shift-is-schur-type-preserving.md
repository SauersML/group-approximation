---
rg: 2
id: packet-headed-toeplitz-shift-is-schur-type-preserving
kind: claim
title: The packet-headed Toeplitz shift preserves full Schur types and supplies no branching contraction
distinct_from:
  reset-ray-hnn-return-is-stationary: that computes stationarity after the finite selector reset; this computes the coefficient algebra map of the new packet-headed Toeplitz envelope before any reset.
  schur-toeplitz-head-is-matrix-amplified-forbidden-algebra: that identifies every finite head with matrix copies of the forbidden algebra; this observes that the self-embedding only shifts those identical copies.
  oriented-schur-child-branching-identity: that gives the desired factor-two restriction through the Q child; this proves the present self-map never applies that restriction.
---

Let `A_f^-=P_fk[B_f]P_f` and let `sigma` be the endomorphism of
`schur-toeplitz-envelope-has-proper-self-embedding`. Since
`epsilon(A_f^-)=0`,

```text
sigma(a)=xay,                    a in A_f^-.              (PTS1)
```

For every `n`, the map

```text
A_f^-->x^nA_f^-y^n,             a |->x^nay^n             (PTS2)
```

is an algebra isomorphism, with inverse `b |->y^nbx^n`. Consequently every
Wedderburn block, irreducible dimension, and full-packet multiplicity type is
preserved exactly by the Toeplitz shift. The prefix theorem merely gives

```text
F_N^- isomorphic to M_N(A_f^-),                            (PTS3)
```

a matrix amplification of identical full blocks.

In particular the current ascending HNN relation identifies one full
forbidden packet with the next full forbidden packet. It never restricts
through `B_f^Q`, never separates the two child-simple labels, and cannot
justify the coefficient `lambda=1/2` from
`oriented-schur-child-branching-identity`.

Thus the packet-headed Toeplitz envelope closes three genuine tasks—literal
predicate orientation, proper self-similar addressing, and exact
finite-dimensional root invisibility—but not the Schur multiplicity return.
Any contraction proof must additionally install the child Morita wire of
`toeplitz-schur-child-masa-recurrence` (or another non-type-preserving
finite-dimensional channel). Iterating `(PTS1)` alone is a stationary type
flow.
