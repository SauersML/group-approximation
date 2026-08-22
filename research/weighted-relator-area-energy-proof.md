---
rg: 2
id: weighted-relator-area-energy-proof
kind: route
title: Telescope the diagram and apply weighted Cauchy--Schwarz
target: weighted-relator-area-energy-bound
requires: []
---

Unitary invariance under conjugation and telescoping the chosen identity
decomposition give

```text
||w(U)-1||_2<=sum_r m_r||r(U)-1||_2.
```

Weighted Cauchy--Schwarz bounds the square of the right side by

```text
(sum_r p_r||r(U)-1||_2^2)(sum_r m_r^2/p_r),
```

proving `(WAE2)--(WAE3)`.  The final optimization follows from
`sum_r m_r^2/p_r >= (sum_r m_r)^2`, with equality at
`p_r=m_r/sum_s m_s`.
