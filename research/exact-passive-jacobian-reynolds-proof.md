---
rg: 2
id: exact-passive-jacobian-reynolds-proof
kind: route
title: Differentiate the two order-three residuals
target: exact-passive-jacobian-is-two-reynolds-expectations
requires: []
---

Let `X_h(t)=X exp(th)` with `[h,R]=0`, and set

```text
A=XS^2,  B=XRS,  k_1=Ad_(S^(-2))(h),  k_2=Ad_(S^(-1))(h).
```

Moving the exponential past `S^2`, and past `R` and then `S`, gives the
exact identities

```text
X_h(t)S^2=A exp(tk_1),       X_h(t)RS=B exp(tk_2).       (1)
```

For any `U^3=1`, differentiating `(U exp(tk))^3` at zero and
right-trivializing at `U^3=1` gives

```text
k+Ad_U(k)+Ad_U^2(k)=3 E_U(k),                            (2)
```

where `E_U=(I+Ad_U+Ad_U^2)/3` is the trace-preserving conditional
expectation onto `{U}'`.  Applying `(2)` to the two identities in `(1)`
shows

```text
DF_X(h)=3(E_A k_1,E_B k_2).                              (3)
```

Conjugation by `S^(-2)` and `S^(-1)` is a unitary complete isometry at
every matrix level.  Thus `(3)` is exactly the asserted two-Reynolds
column up to the stated complete isometries.  Each `E_U` is completely
contractive, so the column has a universal cb bound; the only unresolved
issue is the uniform cb norm of its gauge-normal inverse on its range.
