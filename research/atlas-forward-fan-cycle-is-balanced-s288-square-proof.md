---
rg: 2
id: atlas-forward-fan-cycle-is-balanced-s288-square-proof
kind: route
title: Put all four finite vertices on their common regular degree
target: atlas-forward-fan-cycle-is-balanced-s288-square
requires:
  - atlas-noncentral-first-core-cycle-has-s288-regular-star
  - atlas-shared-forward-fan-is-2four-by-3two
---

Use the finite vertices

```text
Q=Q96,        F'=S3 x S3,       C=C2^4:(C3 x C3),       J=S4
|Q|=96,       |F'|=36,          |C|=144,                 |J|=24.
```

Their marked edge groups around the square are

```text
Q intersect F' =<c,u>~=V4,             order 4,
F' intersect C =<r,z>~=C3 x C3,        order 9,
C intersect J  =<b>~=C2,               order 2,
J intersect Q  =<c,t>~=A4,             order 12.          (SQ-1)
```

Take respectively `3,8,2,12` copies of the four regular actions.  Each has
degree 288.  Their restrictions around `(SQ-1)` are

```text
3 Reg(Q)|_V4   =72 Reg(V4) =8 Reg(F')|_V4,
8 Reg(F')|_A   =32 Reg(A)  =2 Reg(C)|_A,
2 Reg(C)|_B    =144 Reg(B) =12 Reg(J)|_B,
12 Reg(J)|_A4  =24 Reg(A4) =3 Reg(Q)|_A4.              (SQ-2)
```

Choose a spanning tree of the square.  The three corresponding labeled
actions can be aligned successively by permutation conjugacies, preserving
faithfulness of every vertex.  The last edge asks whether the two induced
copies of its subgroup are conjugate by the centralizer of the already fixed
tree data.  This is one finite double-coset condition; `(SQ-2)` proves its two
marginal permutation characters agree exactly but does not assert that the
double coset is nonempty.
