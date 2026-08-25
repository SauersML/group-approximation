---
rg: 2
id: wandering-complement-capacity-proof
kind: route
title: Compare the trace square of the sum of the wandering exits
target: wandering-complement-contractions-pay-fanizza-mirror
requires: []
---

First compute the exact complement ledger.  Since `Q` and `E` have equal
trace and `E=F+H`,

```text
tr(A)=tr((1-E)Q)
     =tr(E)-tr(FQ)-tr(HQ).                              (WCP1)
```

Moreover

```text
tr(F)-tr(FQ)=||(1-Q)F||_2^2,
tr(HQ)=||QH||_2^2=b^2.
```

As `tr(E)-tr(F)=h`, this gives

```text
tr(A)=h+||(1-Q)F||_2^2-b^2>=h-b^2.                    (WCP2)
```

Set `c=tr(A)=tr(A_i)` and `S=sum_i A_i`.  Positivity gives
`tr(A_iA_j)>=0`, while `(WCM2)` gives `tr(A_iA_j)<=eta^2`.  Also
`0<=A_i<=1` implies `tr(A_i^2)<=c`.  Therefore

```text
tr(S^2)
 <=N c+N(N-1)eta^2.                                    (WCP3)
```

Normalized-trace Cauchy--Schwarz gives

```text
(N c)^2=tr(S)^2<=tr(S^2),
```

so

```text
c^2<=c/N+eta^2.
```

Solving the quadratic and using
`sqrt(x^2+y^2)<=x+y` yields

```text
c<=1/(2N)+sqrt(1/(4N^2)+eta^2)<=1/N+eta.              (WCP4)
```

Combine `(WCP2)` and `(WCP4)` to obtain `(WCM3)--(WCM4)`.
