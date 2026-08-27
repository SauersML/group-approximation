---
rg: 2
id: unitary-trace-energy-transfer
kind: claim
title: Average trace domination propagates small Hilbert--Schmidt energy without constructing conjugators
---

Let `(M,tau)` be a finite tracial von Neumann algebra with normalized trace,
and let

```text
B,T_1,...,T_m in U(M).
```

If for some `eps>=0`

```text
sum_i Re tau(T_i) >= m Re tau(B) - eps,
```

then

```text
sum_i ||T_i-1||_2^2
 <= m ||B-1||_2^2 + 2 eps.                       (TRACE-TRANSFER)
```

No relation among the `T_i` is required and no conjugating unitaries have to be
constructed.

This is strictly weaker data than the opaque-conjugacy interface of
`unitary-star-conjugacy-hs-collapse`: for Hilbert--Schmidt collapse it is enough
to transfer one **scalar average trace** from the hub to the leaves.  In
particular, a compiler whose only output is a lower bound on the average real
trace of several covariance opcodes can replace a compiler that explicitly
synthesizes one unitary transport register per opcode.
