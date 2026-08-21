---
rg: 2
id: controlled-swap-matrix-corner-proof
kind: route
title: Compute the controlled-swap commutator on the capacity decomposition
target: controlled-swap-wordizes-matrix-corner-without-adjoint-dilution
requires: []
---

# Block proof

Decompose the two-copy module by `Q` and `I-Q`.  The controlled swap

```text
T=[[I-Q,Q],[Q,I-Q]]
```

is the identity on the second summand and the full coordinate flip on the
first.  For `A=diag(R,I)` with `[R,Q]=0`, the commutator `ATA^*T` is therefore
the identity off `Q` and `diag(R,R^*)` on `Q`.  Taking normalized trace on
the two-copy algebra proves

```text
||ATA^*T-I||_2^2=||(R-I)Q||_2^2.
```

The switch truth table in the three commuting character bits `(q,k,t)` is
`t=qk`.  It is not closed under addition, so commuting-involution relators
cannot produce it.  Finally, replacing `Q` by the left-support projection on
`L^2(M_d)` measures the whole-module return, which the exact PAZ vector
semantics does not control.  These calculations prove both the exact gain
and its boundary.
