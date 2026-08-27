---
rg: 2
id: independent-finite-clock-row-pvm-proof
kind: route
title: Measure clock off-diagonal mass by its commutator and round all outcomes together
target: independent-finite-clocks-round-to-arbitrary-row-pvms
requires:
  - outcome-count-free-subpovm-completion
---

Orthogonality of the spectral blocks gives

```text
tau(Q)-sum_v tau((QE_vQ)^2)
 =sum_(v!=w)||E_vQE_w||_2^2.                          (FCP1)
```

Moreover

```text
E_v[Q,U]E_w=(lambda_w-lambda_v)E_vQE_w,
```

so the right side of `(FCP1)` is at most
`Delta_N^(-2)||[Q,U]||_2^2`.  Apply simultaneous POVM orthogonalization in
`QMQ`; there is no missing mass and its constant-nine bound gives `(FCR2)`.
Independent clocks can realize unrelated spectral multiplicities in exact
models, so no row-conjugacy restriction has been introduced.

