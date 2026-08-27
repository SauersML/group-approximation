---
rg: 2
id: leavitt-multiplicative-trace-floor-proof
kind: route
title: Prove the contraction product inequality and solve its quadratic floor
target: leavitt-multiplicative-trace-floor
requires: []
artifacts:
  - GroupApproximation/Sofic/LeavittTraceFloor.lean
---

Approximate right inverses force `||T_0||_2` and `||S_1||_2` to be at least
`1-epsilon`.  Positivity of the two Gram deficiencies gives, for
contractions `A,B`,

```text
||AB||_2^2 >= ||A||_2^2 + ||B||_2^2 - 1.
```

Applying this to `T_0 S_1` yields
`epsilon^2 >= 2(1-epsilon)^2-1`, whose smaller root is `2-sqrt(3)`.
The sharp max-defect theorem and the unitary-pairing form are kernel-checked
in the cited Lean module.
