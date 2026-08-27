---
rg: 2
id: schur-violation-density-gives-contraction-proof
kind: route
title: Add the violation surplus and divide by one plus the soundness gap
target: schur-violation-density-gives-contraction
requires:
  - oriented-schur-child-branching-identity
  - contractive-computation-ladder
---

From `(SVG1)` and `(SVG2)`,

```text
c_n=a_n+v_n>=(1+beta)a_n-delta_n.
```

Together with `(SVG3)` this gives

```text
a_(n+1)>=(1+beta)a_n-delta_n-eta_n.
```

Divide by `1+beta` to obtain `(SVG4)`. Under `(SVG5)`, `(SVG4)` is `(CCL1)`
with `lambda=(1+beta)^(-1)`. The geometric-polynomial series

```text
sum_(n>=0) lambda^n(n+1)^k
```

converges, so `contractive-computation-ladder` gives `(SVG6)`.

For the packet interpretation, sum `(OCB2)` over selector sectors:

```text
sum_x m_Q(x)
 =sum_(f(x)=0)m_B(x)+2sum_(f(x)=1)m_B(x)
 =sum_x m_B(x)+sum_(f(x)=1)m_B(x).
```

After multiplying by the fixed baseline packet size and normalizing by the
ambient matrix dimension, this is `(SVG2)` with `v_n` equal to forbidden
sector mass. No complement is discarded or estimated.
