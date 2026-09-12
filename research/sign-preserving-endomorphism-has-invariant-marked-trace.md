---
rg: 2
id: sign-preserving-endomorphism-has-invariant-marked-trace
kind: claim
title: A sign-preserving endomorphism cannot have an empty invariant marked trace face
distinct_from:
  finite-packet-cannot-realize-absorbing-contraction: that uses the negative regular summand of one finite group to refute a finite absorbing chain; this is an infinite-dimensional fixed-point theorem for endomorphism dynamics.
  trace-blindness-sharpness: that says normalized trace cannot see proper finite-index inclusions; this constructs an invariant trace and does not compare indices.
---

Let `A` be a unital C-star algebra, let `J` be a central self-adjoint unitary,
and let `alpha:A->A` be a unital star endomorphism with `alpha(J)=J`.  If there
is a tracial state `tau` with `tau(J)=-1`, then there is such a tracial state
`tau_infinity` satisfying

```text
tau_infinity after alpha = tau_infinity.                         (SPE1)
```

In particular, injectivity or non-surjectivity of `alpha` cannot make the
sign-alive invariant trace set empty.  Surjectivity of the induced map on a
dual state space is unnecessary.

