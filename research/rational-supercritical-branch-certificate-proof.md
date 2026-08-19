---
rg: 2
id: rational-supercritical-branch-certificate-proof
kind: route
title: Pair the capacity inequality with the positive rational subeigenvector
target: rational-supercritical-branch-certificate
requires: []
---

Rewrite `(RBC1)` as

```text
x + e >= A x.
```

Pair both sides with the positive vector `y`.  Positivity preserves the
coordinatewise inequality, so

```text
y . x + y . e >= y . (A x) = (A^T y) . x.
```

By `(RBC2)` and `x>=0`,

```text
(A^T y) . x >= (1+kappa) y . x.
```

Combining the last two displays and cancelling `y.x` gives

```text
y . e >= kappa y . x,
```

which is `(RBC3)`.

Every operation is rational once `A,y,kappa` are supplied.  The
Perron--Frobenius theorem is useful for proving that a supercritical strongly
connected matrix admits such certificates, but it is not needed to check one.