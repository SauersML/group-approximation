---
rg: 2
id: finite-control-acceptance-leakage-proof
kind: route
title: Resolve the block unitary output over all nonzero control atoms
target: finite-control-acceptance-leakage-is-a-zero-corner-sum
requires: []
---

Unitary invariance and `P_0X^a=X^aP_a` give

```text
||P_0X^aWP_0||_2=||P_aWP_0||_2.
```

Sum the squared norms over `a!=0` and use orthogonality of the `P_a`:

```text
sum_(a!=0)||P_aWP_0||_2^2
 =||(I-P_0)WP_0||_2^2
 =||WP_0||_2^2-||P_0WP_0||_2^2.
```

Since `W` is unitary, `||WP_0||_2^2=tau(P_0)`, proving `(FCL1)`.
The operator-norm bound gives
`||P_0WP_0||_2^2<=rho^2tau(P_0)`, proving `(FCL2)`.

