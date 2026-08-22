---
rg: 2
id: dense-offdiagonal-leavitt-heisenberg-packet
kind: claim
title: A second root path moves the dual-prefix phase from the sparse diagonal to its dense complement
distinct_from:
  leavitt-prefixes-form-exponential-heisenberg-packet: that uses the identity pairing and places the common sign only on equal prefixes; this adds one constant root path and realizes the complementary pairing.
---

**ESTABLISHED.**

Work over the relative binary Leavitt envelope in characteristic two, with
active idempotent `A` and depth-`n` coefficients

```text
t_alpha s_beta=delta_(alpha,beta) A.
```

Inside `St_5(R)` define

```text
Xhat_alpha=x_12(A)x_13(t_alpha),
Yhat_beta =x_24(A)x_34(s_beta),
Jhat      =x_14(A).                                      (DOL1)
```

The two factors in each displayed product commute.  The resulting
involutions commute within each family and satisfy

```text
[Xhat_alpha,Yhat_beta]
  =Jhat^(1+delta_(alpha,beta)).                           (DOL2)
```

Thus the common sign occurs on every unequal prefix pair, of density
`1-2^(-n)`.  For `D=2^n`, the pairing matrix is `K=I+11^T` over `F_2`.
Because `D` is even, `K` is invertible.  Hence the exact packet is again a
rank-`D` Heisenberg packet: every `Jhat=-1` representation sector has
dimension divisible by `2^D`.

Moreover, a uniformly random unequal pair proves `(DOL2)` by cancelling only
until the first prefix mismatch.  The number of coefficient cancellations
has uniformly bounded first and second moments; the exceptional equal pairs
cost `n` and have probability `2^(-n)`.  The raw coefficient calculation
therefore has both positive phase density and bounded average cancellation
cost.

This does not by itself yield an HS obstruction.  The rank of `K` is carried
by the rare diagonal corrections, and
`dense-offdiagonal-packet-has-linear-dimensional-average-models` gives an
explicit canonical-moment countermodel to any argument using only average
cross-relation energy.
