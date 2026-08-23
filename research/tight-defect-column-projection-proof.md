---
rg: 2
id: tight-defect-column-projection-proof
kind: route
title: Normalize the defect Gram operator and reflect
target: tight-defect-column-solves-algebraic-projection-crt
requires:
  - shared-involution-right-ideal-interpolation-criterion
---

Set `K=DD^*`.  Equation `(TDC3)` gives

```text
K^2=(DD^*D)D^*=lambda DD^*=lambda K.                 (TDCP1)
```

Hence `p=K/lambda` is self-adjoint and idempotent.  The same equation also
gives

```text
pD=D.                                                 (TDCP2)
```

Compatibility `(TDC1)` implies orthogonality of the sum and difference
columns:

```text
D^*(X+Y)
=(X-Y)^*(X+Y)
=X^*X+X^*Y-Y^*X-Y^*Y=0.                              (TDCP3)
```

Therefore

```text
p(X+Y)=lambda^(-1)D[D^*(X+Y)]=0.                     (TDCP4)
```

Since `2X=(X+Y)+D`, equations `(TDCP2)--(TDCP4)` yield

```text
pX=D/2=(X-Y)/2.                                       (TDCP5)
```

On the `i`th column this reads

```text
pq_i=(q_i-A_iq_i)/2=[(1-A_i)/2]q_i,                  (TDCP6)
```

which is `(TDC5)`.  The projection-CRT criterion now gives the reflection
`B=1-2p` and all claimed interpolation equations.
