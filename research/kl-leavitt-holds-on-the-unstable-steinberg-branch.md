---
rg: 2
id: kl-leavitt-holds-on-the-unstable-steinberg-branch
kind: route
title: On the HS-unstable Steinberg branch the Leavitt unit group satisfies Kervaire--Laudenbach
target: kl-holds-over-binary-leavitt-unit-group
requires: [leavitt-steinberg-hs-unstable, leavitt-steinberg-hs-stability-fork, leavitt-gl-equals-el-and-perfect-unit-group, kervaire-laudenbach-holds-for-hyperlinear]
---

Assume `U = St_5(L)` is not normalized-HS stable, `L = L_(F_2)(1,2)`.  The
unstable branch of `leavitt-steinberg-hs-stability-fork` makes
`Q = EL_4(L)` hyperlinear.  A four-leaf complete prefix code gives
`L = M_4(L)`, so `L^x = GL_4(L)`, and `GL_4(L) = EL_4(L)` by
`leavitt-gl-equals-el-and-perfect-unit-group`.  Hence `R^x` is hyperlinear,
and `kervaire-laudenbach-holds-for-hyperlinear` injects the coefficients of
every nonsingular equation.

Together with `leavitt-kl-violation-selects-the-stable-steinberg-branch`,
this places the Leavitt Kervaire--Laudenbach decision downstream of the
Steinberg fork: a violation forces the stable branch, and the unstable branch
refutes every violation.  Only on the stable branch is the question open.
