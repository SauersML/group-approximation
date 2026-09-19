---
rg: 2
id: oriented-schur-restriction-mass-identity-proof
kind: route
title: Split the multiplicity sum into active and inactive sectors
target: oriented-schur-restriction-mass-identity
requires:
  - predicate-rank-gate-doubles-restriction-multiplicity
---

Write `G={x:f(x)=1}` and `F={x:f(x)=0}`. The restriction formula gives

```text
a_A=2 sum_(x in G)h(x)m(x)+sum_(x in F)h(x)m(x).
```

Therefore

```text
(1/2)a_A+(1/2)b_inactive
 =sum_(x in G)h(x)m(x)+sum_(x in F)h(x)m(x)
 =a_B.
```

This is `(OSR1)`.

