---
rg: 2
id: approximate-orthogonal-bridge-proof
kind: route
title: Pair the two bridges and compress the transverse block
target: approximate-orthogonal-bridge-transfers-hs-mass
requires: []
---

With the normalized HS inner product,

```text
||B||_2^2
 = <B,B'> + <B,B-B'>.                                         (1)
```

Cauchy--Schwarz bounds the second term by `eta||B||_2`.  For the first,

```text
<B,B'>=tr(R Q P Q' R)=tr(R C R).                               (2)
```

Schatten duality and compression give

```text
|tr(R C R)| <= ||C||_1 <= ||C||_2.                             (3)
```

Combining `(1)--(3)` proves `(AB2)`.
