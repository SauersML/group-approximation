---
rg: 2
id: affine-frobenius-projection-crt-via-tight-defect-frame
kind: route
title: Manufacture the Frobenius CRT projection from a cubic tight-frame identity
target: affine-frobenius-algebraic-projection-crt
requires:
  - tight-defect-column-solves-algebraic-projection-crt
  - affine-frobenius-tight-defect-column-frame
---

For each variable `x`, apply the established tight-defect theorem to the
data `(AFT1)--(AFT2)`.  It gives the finite-support projection

```text
p_x=lambda_x^(-1)D_xD_x^*.
```

Equation `(TDC5)` is exactly the incidence prescription `(AFPC2)`.  The
open frame claim also preserves the fixed PVMs and the strict weighted
deficit, so every clause of `affine-frobenius-algebraic-projection-crt`
holds.
