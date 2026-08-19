---
rg: 2
id: unitary-trace-energy-transfer-proof
kind: route
title: Expand Hilbert--Schmidt distance through the trace
 target: unitary-trace-energy-transfer
requires: []
---

For every unitary `T` in a finite tracial algebra,

```text
||T-1||_2^2
 = tau((T-1)^*(T-1))
 = 2 - tau(T) - tau(T^*)
 = 2 - 2 Re tau(T).
```

Therefore

```text
sum_i ||T_i-1||_2^2
 = 2m - 2 sum_i Re tau(T_i)
 <= 2m - 2m Re tau(B) + 2 eps
 = m ||B-1||_2^2 + 2 eps.
```

This proves `(TRACE-TRANSFER)` exactly.  The argument uses only traciality and
unitarity and is independent of matrix size, multiplicity, or any semantics of
the opcodes.
