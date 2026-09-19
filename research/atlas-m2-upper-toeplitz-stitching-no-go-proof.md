---
rg: 2
id: atlas-m2-upper-toeplitz-stitching-no-go-proof
kind: route
title: Pass both Laurent residuals to every diagonal flag quotient
target: atlas-m2-kernel-phases-cannot-upper-toeplitz-stitch
requires:
  - atlas-multiplicity-two-joint-kernel-slice-is-empty
  - atlas-repeated-h6-gauge-is-one-gl2m-coordinate
---

An invertible block-upper-triangular matrix has an upper-triangular inverse.
Therefore every product in `T`, `T^-1`, and fixed block-diagonal coefficient
matrices preserves the standard block flag.  On the `i`th associated-graded
quotient, evaluation commutes with passage to the diagonal block:

```text
gr_i(q_w(T)-I)=q_w(T_i)-I.                            (UTP1)
```

For any flag-preserving linear map `L`, the associated graded of `ker L`
injects into `ker(gr L)`.  Hence

```text
rank(L) >= sum_i rank(gr_i L).                        (UTP2)
```

Apply `(UTP2)` to the two kernel residuals and use the exact rank pairs
`(0,1)` and `(2,0)` from the multiplicity-two calibration.  This gives
`(UTS2)`.  Minimizing `max(n_A,2(N-n_A))` over `0<=n_A<=N` gives `(UTS3)`.
