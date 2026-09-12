---
rg: 2
id: leavitt-first-mixed-relator-proof
kind: route
title: Conjugate one nonzero-degree root by the constant Weyl swap and apply amalgam normal form
target: leavitt-first-mixed-amenable-face-relator
requires: []
---

As literal upper-triangular matrix groups,

```text
L_0 cap P = U_3(R_0) semidirect T_0 = C_0.
```

The Weyl matrix `w` is not upper triangular, so `w notin C_0`. The Leavitt
gauge grading has `deg(s_0)=1`, while every coefficient in `R_0` has degree
zero. Hence `x_02(s_0),x_12(s_0) notin C_0`. The four syllables in `(FMR1)`
therefore alternate between `L_0\C_0` and `P\C_0`. The normal-form theorem for
group amalgams makes `r` nontrivial in `A_0`.

Inside `L`, the characteristic-two Whitehead word `w` interchanges the first
two matrix coordinates. Direct matrix conjugation gives

```text
w x_02(a) w^(-1)=x_12(a)              (a in R).
```

Taking `a=s_0` proves that `(FMR1)` maps to one. No reduced identity can have
syllable length one, two, or three: after cyclic reduction, a new relation in
an amalgam has even alternating length at least four. Thus this is a shortest
mixed kernel word.
