---
rg: 2
id: finite-elementary-tensor-divisibility-proof
kind: route
title: Divide each first-factor class and take the sum of the external products
target: finite-elementary-tensor-blocks-are-divisible
requires: []
---

Almost divisibility of `Cu(A)` gives, for every `i`, an element `delta_i` with

```text
n delta_i <= alpha_i,       alpha_i' <= (n+1)delta_i.
```

Set

```text
gamma=sum_i (delta_i boxtimes beta_i).
```

The external Cuntz product is additive and order-preserving in each variable.
Therefore

```text
n gamma
 = sum_i ((n delta_i) boxtimes beta_i)
 <= sum_i (alpha_i boxtimes beta_i),
```

and similarly

```text
sum_i (alpha_i' boxtimes beta_i)
 <= sum_i (((n+1)delta_i) boxtimes beta_i)
 = (n+1)gamma.
```

No exactness, nuclearity, simplicity, or hypothesis on `B` is used.
