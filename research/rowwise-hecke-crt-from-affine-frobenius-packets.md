---
rg: 2
id: rowwise-hecke-crt-from-affine-frobenius-packets
kind: route
title: Store every context in an almost-full Frobenius block and solve shared involutions variablewise
target: rowwise-hecke-crt-certificate-for-nonce-bcs
requires:
  - affine-frobenius-packets-solve-local-row-mask-storage
  - affine-frobenius-hecke-crt-shared-involution-interpolation
---

Put

```text
M=sum_(c,x)mu_(c,x),        mu_c=sum_(x in U_c)mu_(c,x).
```

Then `sum_c mu_c=M`.  With both the predicate and incidence masks equal to
the explicit Frobenius complement, the total canonical deficit is exactly

```text
(1/p)sum_c mu_c+(1/p)sum_(c,x)mu_(c,x)=2M/p.          (AFHR1)
```

Choose the first prime `p>2M/Delta` (and satisfying any finite local storage
congruence requirement), so that `(AFHR1)<Delta`.  In the normalized case
`M=1`, it is enough that `p>2/Delta`.  The Frobenius packets realize the one
global PVM for every context and every prescribed rational local marginal.
The interpolation claim adds one global involution per variable and private
large right-ideal masks without changing those PVMs.  These are exactly
`(HCRT1)--(HCRT2)`.
