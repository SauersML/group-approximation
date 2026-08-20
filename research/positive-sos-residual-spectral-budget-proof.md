---
rg: 2
id: positive-sos-residual-spectral-budget-proof
kind: route
title: Compress the residual to the negative spectral side
target: positive-sos-residual-spectral-budget
requires: []
---

Let `P=P_0`.  Since `P` is a spectral projection of `A`, it commutes with
`A`.  On the range of `P` we have `0<=A<=kappa/2`, hence

```text
A(kappa-A) >= (kappa/2) A.
```

Also `PBP>=0`.  Therefore

```text
PRP
 = -P A(kappa-A) P - PBP
 <= -(kappa/2) PAP.
```

Taking the trace and using tracial Cauchy--Schwarz gives

```text
(kappa/2) tau(PA)
 <= -tau(PRP)
 <= |tau(PRP)|
 =  |tau(PR)|
 <= ||P||_2 ||R||_2
 <= eta.
```

This is the first inequality in `(SB1)`.  Since `P` commutes with `A`, another
Cauchy--Schwarz estimate gives

```text
tau(P sqrt(A))^2
 <= tau(P) tau(PA)
 <= 2 eta/kappa,
```

proving the second.

For `(SB2)`, let `Q=P_[a,b]`.  On `[a,b]`,

```text
A(kappa-A) >= c(a,b) 1.
```

Consequently

```text
QRQ
 = -Q A(kappa-A) Q - QBQ
 <= -c(a,b) Q.
```

Taking traces again,

```text
c(a,b) tau(Q)
 <= -tau(QRQ)
 <= ||Q||_2 ||R||_2
 <= sqrt(tau(Q)) eta.
```

If `tau(Q)=0` there is nothing to prove; otherwise divide by
`sqrt(tau(Q))` and square to obtain

```text
tau(Q) <= (eta/c(a,b))^2.
```

No commutation between `A` and `B` is used.  Positivity of the compressed
operator `QBQ` is the only input from the SOS side.
