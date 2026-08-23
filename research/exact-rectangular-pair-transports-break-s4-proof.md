---
rg: 2
id: exact-rectangular-pair-transports-break-s4-proof
kind: route
title: Conjugate one duplicated Weyl pair by identity and swap
target: separate-pauli-branch-transports-do-not-carry-s4
requires:
  - first-leavitt-weyl-cell-has-exact-rectangular-model
  - four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap
---

Specialize `(FWC2)` to `p=2`.  The identities

```text
U_0(X_src,Z_src)U_0^*=(X tensor 1,Z tensor 1),
U_1(X_src,Z_src)U_1^*=(1 tensor X,1 tensor Z)
```

give the two exact branch transports on the same four-dimensional carrier.
Alternation makes `s4(X_src,Z_src,X_src,Z_src)=0`.  The two internal
anticommutation and four cross-commutation identities invoke the exact case
of the four-Pauli calculation, giving
`s4(X_0,Z_0,X_1,Z_1)=8X_0Z_0X_1Z_1`, whose normalized Hilbert--Schmidt norm
is eight.  Thus the polynomial jump occurs at zero relation and transport
defect.
