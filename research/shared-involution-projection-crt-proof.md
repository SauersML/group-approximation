---
rg: 2
id: shared-involution-projection-crt-proof
kind: route
title: Orthogonalize the sum and difference columns and reflect
target: shared-involution-right-ideal-interpolation-criterion
requires: []
---

If `B` satisfies `(SIC2)`, then `BX=Y`.  Since `B` is unitary,

```text
X^*X=Y^*Y.
```

Since `B` is self-adjoint,

```text
X^*Y=X^*BX=(X^*BX)^*=Y^*X.
```

Taking the `(i,j)` matrix entries gives `(SIC4)`.

Conversely, `(SIC3)` gives

```text
(X+Y)^*(X-Y)
 =X^*X-X^*Y+Y^*X-Y^*Y=0.                              (SICP1)
```

Thus `E_+` and `E_-` in `(SIC5)` are orthogonal.  The reflection
`B_0=1-2e_-` fixes `X+Y` and negates `X-Y`, so

```text
B_0X
 =1/2[B_0(X+Y)+B_0(X-Y)]
 =1/2[(X+Y)-(X-Y)]
 =Y.                                                   (SICP2)
```

This proves existence.

For an arbitrary symmetry `B=1-2p`, the equation `BX=Y` is equivalent to

```text
pX=(X-Y)/2.                                            (SICP3)
```

On the `i`th column this is `(SIC8)`.  Adding and subtracting `(SICP3)` from
its image under `p` gives `(SIC7)`, and the implications reverse.  This also
proves the algebraic and stabilized statements.

When the data lie in `M`, both `(X-Y)(X-Y)^*` and its support projection lie
in `M`, proving the von Neumann assertion.

Finally let `p,q` be projections and suppose `qpq` is a projection.  Then

```text
qpq-(qpq)^2=qp(1-q)pq=0.                               (SICP4)
```

The right side is `[(1-q)pq]^*[(1-q)pq]`, so
`(1-q)pq=0`; taking adjoints also gives `qp(1-q)=0`.
Therefore `pq=qp=qpq`.  Applying this with
`qpq=qe_iq=e_iq` proves `(SIC12)`.
