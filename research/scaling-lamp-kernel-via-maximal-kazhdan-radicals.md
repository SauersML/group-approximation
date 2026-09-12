---
rg: 2
id: scaling-lamp-kernel-via-maximal-kazhdan-radicals
kind: route
title: Use the intrinsic maximal-Kazhdan finite-radical closure
target: scaling-lamp-kernel-isomorphism-invariant
requires:
  - maximal-kazhdan-radicals-recover-scaling-lamps
---

An isomorphism preserves property `(T)`, subgroup inclusion, and maximality.
It sends the unique largest finite normal subgroup of a maximal
property-`(T)` subgroup onto the corresponding finite radical of its image.
Consequently every isomorphism `Phi:G->G'` satisfies

```text
Phi(K_T(G))=K_T(G').
```

Applying the prerequisite formula `K_T(E_r)=N_r` at scales `m` and `n`
gives `Phi(N_m)=N_n`, exactly the cross-family assertion.
