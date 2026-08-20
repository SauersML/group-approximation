---
rg: 2
id: positive-sos-residual-spectral-budget-proof
kind: route
title: Compress the residual to the negative spectral side
target: positive-sos-residual-spectral-budget
requires: []
---

Let `P=P_0`. On its range, `0<=A<=kappa/2`, so
`A(kappa-A)>=(kappa/2)A`. Since `PBP>=0`,

```text
PRP=-PA(kappa-A)P-PBP<=-(kappa/2)PAP.
```

Tracial Cauchy--Schwarz gives

```text
(kappa/2)tau(PA)<=|tau(PRP)|<=||P||_2||R||_2<=eta.
```

As `P` commutes with `A`, another Cauchy--Schwarz estimate gives
`tau(P sqrt(A))^2<=tau(P)tau(PA)<=2eta/kappa`, proving `(SB1)`.

For `Q=P_[a,b]`, functional calculus gives
`A(kappa-A)>=c(a,b)` on its range, whence `QRQ<=-c(a,b)Q`. Therefore

```text
c(a,b)tau(Q)<=||Q||_2||R||_2<=sqrt(tau(Q))eta.
```

If `tau(Q)>0`, divide by its square root and square; otherwise the claim is
immediate. This proves `(SB2)` without requiring `A` and `B` to commute.
