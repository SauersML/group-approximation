---
rg: 2
id: pauli-binary-algebra-gap-proof
kind: route
title: Minimize the two-projection conditional-expectation quadratic
target: pauli-binary-algebra-gap
requires: []
artifacts:
  - GroupApproximation/Leavitt/PauliCarrierBinaryGap.lean
  - notes/TRUE_PAULI_CARRIER_BINARY_ALGEBRA_GAP.md
---

Writing `x=tau(EF)`, the squared distance is

```text
1/4 - 8x^2 - (8/7)(1/4-x)^2,
```

with `0 <= x <= 1/8`.  Exact minimization gives `3/28`.  The canonical
overlap `x=1/32` makes the conditional expectation scalar and gives the
stronger `3/16` value.  These inequalities are kernel-checked in the cited
Lean module.
