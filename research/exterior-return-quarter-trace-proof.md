---
rg: 2
id: exterior-return-quarter-trace-proof
kind: route
title: Bound the rank of the off-edge return by its normalized L2 mass
target: exterior-return-loss-has-quarter-trace-support
requires:
  - kt-return-expectation-pays-one-full-edge-principal-angle
---

The Pythagorean calculation `(KPP5)` in
`kt-return-principal-angle-gram-proof` gives

```text
||y||_2^2=||(1-P)x||_2^2>=1-(q+eta)^2.                 (QTP1)
```

The trace-preserving conditional expectation `E_B` is a unital completely
positive map and hence an operator-norm contraction.  Since `x` is unitary,

```text
||y||_infinity
 =||x-E_B(x)||_infinity
 <=||x||_infinity+||E_B(x)||_infinity<=2.              (QTP2)
```

For `p=supp(|y|)`, finite-dimensional functional calculus gives

```text
||y||_2^2=tr(p|y|^2)
          <=||y||_infinity^2 tr(p)
          <=4tr(p).                                    (QTP3)
```

Combining `(QTP1)` and `(QTP3)` proves `(QTS2)` and `(QTS3)`.
