---
rg: 2
id: atlas-a8-six-transvection-commutant-gap
kind: claim
title: Six standard A8 transvections give a dimension-free commutant test with diameter constant fifteen
artifacts:
  - experiments/atlas_a8_transvection_normal_certificates.py
---

Let `lambda_k` be `k` copies of the left regular representation of
`A8 ~= GL_4(F2)` and let

```text
S={t01,t10,t12,t21,t23,t32}
```

be the six adjacent standard transvections.  For every operator `X` with
`||X||_op<=1`,

```text
dist_2(X,lambda_k(A8)')
 <= 15 ( sum_(s in S) ||[X,lambda_k(s)]||_2^2 )^(1/2). (A8-6COMM)
```

The constant is independent of the amplification `k`.  The exact finite audit
shows that the directed Cayley diameter of `A8` in this six-transvection
alphabet is exactly `15`.

Thus a compiler does not need a full-chart decoder object: controlling six
chart covariance residuals is already a complete quantitative test for the
regular `A8` commutant.
