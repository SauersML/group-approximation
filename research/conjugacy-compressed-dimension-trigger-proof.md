---
rg: 2
id: conjugacy-compressed-dimension-trigger-proof
kind: route
title: Use unitary invariance and one triangle inequality
target: conjugacy-compressed-dimension-trigger
requires: []
---

For a unitary evaluation `A=a_n(U)` and `R=r(U)`,

```text
||A^* R A-I||_2 = ||A^*(R-I)A||_2 = ||R-I||_2,
```

by two-sided unitary invariance of normalized Hilbert--Schmidt norm.  This is
`(CCD1)` with no word-length factor.  Under `(CCD2)`, the triangle inequality
and `||r(U)-1||_2<=Def(U)` give

```text
||w(U)-1||_2
 <= ||w(U)-c_(N(d))(U)||_2 + ||c_(N(d))(U)-1||_2
 <= (C+1) Def(U),
```

which is `(CCD3)`.  No statement here bounds the first term without the
explicit hypothesis `(CCD2)`.

