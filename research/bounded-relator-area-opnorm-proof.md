---
rg: 2
id: bounded-relator-area-opnorm-proof
kind: route
title: Telescope the conjugated relator factors
target: bounded-relator-area-controls-opnorm-word-defect
requires: []
---

For each factor

```text
V_k=g_k(U) r_k(U)^(epsilon_k) g_k(U)^(-1),
```

unitary invariance and
`||r_k(U)^(-1)-I||_op=||r_k(U)-I||_op` give

```text
||V_k-I||_op <= Def_R(U).
```

For unitary factors, repeated insertion of intermediate products gives

```text
||V_1...V_A-I||_op <= sum_(k=1)^A ||V_k-I||_op.
```

Substitution proves `(BRA1)`.

