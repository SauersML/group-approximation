---
rg: 2
id: character-decision-tree-entropy-proof
kind: route
title: Apply Kraft inequality to the character leaves
target: sequential-character-recentering-has-decision-tree-loss
requires: []
---

If the leaf depths are `d_1,...,d_N`, the prefix-free binary tree satisfies
Kraft's inequality

```text
sum_(a=1)^N 2^(-d_a)<=1.
```

Convexity of `2^(-x)` gives

```text
2^(-(1/N)sum_a d_a)
 <=(1/N)sum_a2^(-d_a)<=1/N.
```

Taking base-two logarithms proves `(SCR1)`.
