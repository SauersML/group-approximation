---
rg: 2
id: multiscale-square-function-checksum-proof
kind: route
title: Iterate the recurrence and apply weighted Cauchy--Schwarz
target: multiscale-square-function-checksum-forces-hs-floor
requires: []
---

Iterating `(MSC1)` to depth `N` gives

```text
a_0<=lambda^N a_N+C sum_(n<N)lambda^n s_n.            (MSCP1)
```

The terminal term tends to zero because `a_N<=1`.  Weighted
Cauchy--Schwarz gives

```text
sum_n lambda^n s_n
 <=(sum_n lambda^n)^(1/2)
   (sum_n lambda^n s_n^2)^(1/2)
 <=sqrt(K E/(1-lambda)).                              (MSCP2)
```

This proves `(MSC3)--(MSC4)`.  For `(MSC5)`, orthogonality of the domain
projections gives the Pythagorean identity

```text
sum_n||D P_n||_2^2=||D(sum_n P_n)||_2^2<=||D||_2^2.   (MSCP3)
```

