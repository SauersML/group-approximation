---
rg: 2
id: positive-mass-four-pauli-pi-proof
kind: route
title: Telescope s4 through the contraction and use its Pauli unitary term
target: positive-mass-four-pauli-intertwiner-forces-pi-gap
requires: []
---

Amitsur--Levitzki gives `s4(C)=0` because all four `C_j` lie in one copy of
`M_2 tensor I`.  For each of the twenty-four degree-four monomials, move `T`
from right to left one letter at a time using
`D_jT=TC_j+(D_jT-TC_j)`.  All other factors are contractions.  Each
`epsilon_j` occurs once in every monomial, so

```text
||s4(D)T-Ts4(C)||_2<=24 sum_j epsilon_j.              (PMP1)
```

Write `V=D_1D_2D_3D_4`, which is unitary.  Since `T` is a contraction,

```text
8||T||_2
 =||8VT||_2
 <=||(8V-s4(D))T||_2+||s4(D)T||_2
 <=epsilon_PI+24 sum_j epsilon_j.                     (PMP2)
```

This is `(PMI1)`.
