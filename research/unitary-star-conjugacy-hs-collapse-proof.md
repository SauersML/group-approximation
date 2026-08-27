---
rg: 2
id: unitary-star-conjugacy-hs-collapse-proof
kind: route
title: Conjugation is an HS isometry, so each star edge costs only its own residual
target: unitary-star-conjugacy-hs-collapse
requires: []
---

For every leaf `i`, the triangle inequality gives

```text
||T_i-1||_2
 <= ||T_i-A_iBA_i^*||_2 + ||A_iBA_i^*-1||_2.
```

Normalized Hilbert--Schmidt distance is invariant under unitary conjugation,
so

```text
||A_iBA_i^*-1||_2=||B-1||_2<=delta.
```

The first term is at most `eta`; hence

```text
||T_i-1||_2<=eta+delta.
```

Taking the maximum proves `(STAR-HS)`.  In particular no estimate on `A_i`, no
consistency between different `A_i`, and no group law for the conjugators is
used anywhere.
