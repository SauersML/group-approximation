---
rg: 2
id: parity-twist-commutant-copy-proof
kind: route
title: Multiply every old intertwiner by the parity implementer
target: parity-twist-copies-the-old-commutant-into-the-excess
requires: []
---

Since `alpha(Lambda)<=Lambda`, restriction reverses containment and gives
`C_0<=C_1`.  If `X in C_0` and `g in Lambda`, then

```text
(Xq)rho(alpha(g))
 =X rho(alpha(g))q
 =rho(alpha(g))Xq,
```

so `C_0q<=C_1`.  Right multiplication by the unitary `q` preserves the
Hilbert--Schmidt inner product and dimension.

For `Y,X in C_0`, `Ad(rho(p))Y=Y`.  The parity relation and `J=-1` give
`rho(p)q rho(p)^*=-q`; because `X` commutes with `rho(p)`,

```text
Ad(rho(p))(Xq)=-Xq.
```

The `+1` and `-1` eigenspaces of the unitary adjoint action are orthogonal,
proving `(PTC2)--(PTC3)`.

Equation `(PTC4)` is the commutator product rule.  For `(PTC5)`, use unitary
invariance of the inner product to write

```text
<Y,Xq>=<Ad(p)Y,Ad(p)(Xq)>
```

and subtract `<Y,-Xq>`.  Cauchy--Schwarz gives the displayed bound.  Applying
these pointwise estimates to fixed spectral windows gives the stated robust
interpretation; the positive-density premise itself is not asserted.
