---
rg: 2
id: kt-strong-nielsen-models-give-reduced-mf
kind: route
title: Integrate the strong Nielsen covariant pair into a faithful norm-corona representation
target: kt-double-reduced-cstar-is-mf
requires:
  - kt-strong-nielsen-covariant-microstates
  - kt-double-is-nielsen-semidirect-product
---

Let

```text
Q=prod_n M_(d_n) / directSum_n M_(d_n).
```

Equations `(SNM2)--(SNM3)` say that

```text
g |-> [U_n(g)],                  b_x |-> [V_n(x)]
```

is an exact covariant representation of `(N,G,alpha)` in `U(Q)`.  Since `N`
is free on the `b_x`, the semidirect-product universal property and `(KNS2)`
give a group homomorphism

```text
rho:D=N semidirect_alpha G -> U(Q),
rho(a,g)=[W_n(a,g)].                                      (SNG1)
```

For `z=sum_j c_j(a_j,g_j) in C[D]`, `(SNM5)` says

```text
||rho(z)||=||lambda_D(z)||.                               (SNG2)
```

Thus the integrated map on `C[D]` is reduced-norm isometric.  It extends by
completion to an injective star homomorphism

```text
C*_r(D)->Q.
```

Therefore `C*_r(D)` is MF.  The trace clause `(SNM6)` is not needed for
injectivity; it records that this embedding also selects the canonical
trace.
