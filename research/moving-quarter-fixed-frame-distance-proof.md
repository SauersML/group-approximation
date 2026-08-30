---
rg: 2
id: moving-quarter-fixed-frame-distance-proof
kind: route
title: Compare the pulled-back quarter source with the balanced Hecke half
target: quarter-native-chart-pays-fixed-hecke-displacement
requires:
  - b2-b3-pair-full-hecke-four-native-sectors
---

Put `A=Q(1-t)/2`.  The four-sector theorem gives

```text
tau(A)=q/2.                                              (1)
```

For `E<=Q` with `tau(E)=beta=q-eta`, let `B<=E` be as in the claim.  For
two projections,

```text
||A-B||_2^2=tau(A)+tau(B)-2tau(AB)
           >=tau(A)-tau(B),                             (2)
```

because `tau(AB)=tau(BAB)<=tau(B)`.  Since `B(Q-E)=0`, orthogonality of
the right supports `E` and `Q-E` gives

```text
||(A-B)E||_2^2
 =||A-B||_2^2-||(A-B)(Q-E)||_2^2
 =||A-B||_2^2-||A(Q-E)||_2^2
 >=||A-B||_2^2-eta.                                    (3)
```

The upper half of `(QMD2)` gives

```text
tau(B)<=(1/4+zeta)beta
       =(1/4+zeta)(q-eta).                              (4)
```

Combining `(1)--(4)` yields

```text
||(A-B)E||_2^2
 >=q/2-(1/4+zeta)(q-eta)-eta
  =(1/4-zeta)q-(3/4-zeta)eta.                           (5)
```

Taking the positive part gives `(QMD3)`.  Letting `eta,zeta` tend to zero
gives `(QMD4)`, and multiplying the projection difference by two gives the
reflection estimate `(QMD5)`.  The common-source theorem gives
`q=1/8192`; simplifying `sqrt(q)/2` and `sqrt(q)` proves `(QMD6)`.
