---
rg: 2
id: s3-hard-cell-three-channel-data-proof
kind: route
title: Compute the S3 Racah, restriction, and overlap determinants exactly
target: s3-hard-cell-three-channel-data-is-nondegenerate
requires: []
---

For the standard real `S3` module with orthonormal basis `e0,e1`, choose the
orthonormal Clebsch--Gordan inclusions

```text
i_1(1)       =(e0 e0+e1 e1)/sqrt(2),
i_epsilon(1) =(e0 e1-e1 e0)/sqrt(2),
i_sigma(e0)  =(e0 e0-e1 e1)/sqrt(2),
i_sigma(e1)  =-(e0 e1+e1 e0)/sqrt(2).                (S3P1)
```

Identify `epsilon tensor sigma` with `sigma` by the quarter-turn
`J(e0)=e1`, `J(e1)=-e0`.  Compose `(S3P1)` first in tensor positions `12`
and then in positions `23`.  Taking normalized Hilbert--Schmidt inner
products of the resulting three maps gives `(S3C2)`, up to independent row
and column signs.  Direct multiplication uses only
`(1/sqrt(2))^2=1/2` and gives `(S3C3)`.

The restrictions

```text
Res(2)=sigma,
Res(3)=1+sigma,
Res(3 epsilon)=epsilon+sigma
```

give the columns of `(S3C4)`, whose determinant is one.

Finally, the central idempotents of `A` and `B` can contribute to the regular
`GL3(2)` trace only when the two summation elements are mutual inverses in
`A intersect B=S3`.  Expanding both idempotents therefore gives `(S3C6)`.
The restriction Gram matrix for `sigma`, `1+sigma`, `epsilon+sigma` is

```text
[1 1 1; 1 2 1; 1 1 2].
```

Multiplying entry `(lambda,mu)` by `d_lambda d_mu/96`, with dimensions
`2,3,3`, gives `(S3C5)`.  The ordinary three-by-three determinant expansion
is `3/8192`.  All three calculations are finite and independent of the open
microstate extraction problem.
