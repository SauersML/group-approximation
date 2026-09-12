---
rg: 2
id: binary-cut-projection-recurrence-gives-bfe1
kind: claim
title: Any binary sign cut of a projection recurrence satisfies the two-child balance
distinct_from:
  branching-plus-first-hit-exits-forces-hs-floor: that consumes the scalar balance as a hypothesis; this derives it from one localized projection recurrence.
  hard-sign-transport-captures-exit-mass: that lower-bounds the negative-sign output using a source hard sign; this proves that positive and negative output masses exhaust the target projection even without commutation.
---

Let `A,C` be projections, let `V` be unitary, and let `Z` be a self-adjoint
involution in a tracial matrix algebra.  Put

```text
B=VAV^*,       R_+=(I+Z)/2,       R_-=(I-Z)/2,
q=tau(A),      q'=||R_+C||_2^2,   r=||R_-C||_2^2.       (BCR1)
```

Then

```text
q'+r=tau(C),                                           (BCR2)
2q <= q'+r+||A+B-C||_2.                               (BCR3)
```

No commutation between `C` and `Z` is required.  Thus cutting the target of a
two-child projection recurrence into its positive active block and negative
first-hit block gives exactly `(BFE1)`, with

```text
delta=||A+VAV^*-C||_2.                                (BCR4)
```

In the Fanizza application, `A=P_tilde_n`, `V=X_tilde_n`, and
`C=P_tilde_(n+1)` before packet correction.  The product clock makes `Z` the
degree-`2n` E5 hard root on the same level.  Therefore the only remaining
analytic input for `(BFE1)` is a polynomial bound for the **localized
groupified recurrence residual** in `(BCR4)`.  Once that certificate is
proved, the binary cut itself incurs no endpoint drift or projection-rounding
loss.
