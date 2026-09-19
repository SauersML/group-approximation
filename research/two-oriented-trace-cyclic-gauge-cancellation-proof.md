---
rg: 2
id: two-oriented-trace-cyclic-gauge-cancellation-proof
kind: route
title: Add the two cyclic trace deficits and cancel the hidden projection
target: two-oriented-trace-cyclic-returns-cancel-the-gauge
requires: []
---

Finite-dimensional cyclicity gives

```text
tr(Y_i X_i)=tr(X_i Y_i),             i=0,1.             (TGCP1)
```

Inserting this common scalar in `(TGR2)` yields

```text
tr(H-G)<=epsilon_0,                                      (TGCP2)
```

and `(TGR3)` similarly yields

```text
tr(G)<=epsilon_1.                                        (TGCP3)
```

Both quantities are nonnegative by `(TGR1)`.  Adding `(TGCP2)` and
`(TGCP3)` proves `(TGR4)`.  The formulation `(TGR6)` follows by adding the
two one-return inequalities directly.

