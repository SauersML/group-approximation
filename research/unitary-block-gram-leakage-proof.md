---
rg: 2
id: unitary-block-gram-leakage-proof
kind: route
title: Split the unitary source column into target and wrong-target blocks
target: unitary-offdiagonal-block-gram-is-support-leakage
requires: []
---

Unitarity and `f+(1-f)=1` give

```text
e=eJ^*Je=eJ^*fJe+eJ^*(1-f)Je=X^*X+L^*L.               (UBP1)
```

This is `(UBL2)`.  Because `0<=L^*L<=e`, its eigenvalues lie in `[0,1]`;
hence

```text
tau((L^*L)^2)<=tau(L^*L)=||L||_2^2,                   (UBP2)
```

which proves `(UBL3)`.  Finally

```text
R_fJ-JR_e=(1-2f)J-J(1-2e)=2(Je-fJ),                  (UBP3)
```

and right multiplication by `e` gives `(UBL5)`.  Multiplication by the
unitary `J R_e` identifies the norm of the additive row in `(UBP3)` with the
multiplicative word defect `C-1`, proving `(UBL6)`.

