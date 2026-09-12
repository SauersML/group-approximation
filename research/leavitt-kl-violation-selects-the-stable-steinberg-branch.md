---
rg: 2
id: leavitt-kl-violation-selects-the-stable-steinberg-branch
kind: route
title: A Leavitt Kervaire--Laudenbach violation selects the HS-stable Steinberg branch
target: leavitt-steinberg-hs-stable
requires: [kl-violating-equation-over-leavitt-unit-group, kervaire-laudenbach-holds-for-hyperlinear, leavitt-steinberg-hs-stability-fork, leavitt-gl-equals-el-and-perfect-unit-group]
---

Suppose a nonsingular equation over `R^x = L^x`, `L = L_(F_2)(1,2)`, kills a
nontrivial coefficient.  By `kervaire-laudenbach-holds-for-hyperlinear`,
`R^x` is not hyperlinear.  The four-leaf prefix code identifies `L` with
`M_4(L)`, so `R^x = GL_4(L)`, and `GL_4(L) = EL_4(L)` by
`leavitt-gl-equals-el-and-perfect-unit-group`.  Thus `Q = EL_4(L)` is not
hyperlinear.

On the unstable branch of `leavitt-steinberg-hs-stability-fork`, `Q` is
hyperlinear.  Exactly one branch holds, so `U = St_5(L)` is normalized
Hilbert--Schmidt stable, which is the target.

## What this places on record

The Kervaire--Laudenbach falsification lane is not parallel to the Steinberg
stability fork; it lives strictly inside its stable branch.  A violation is a
very special algebraic certificate of that branch: its old-relator identity
supplies the linear energy inequality of
`nonsingular-equations-preserve-matrix-certificates` for a word that is
nontrivial in `Q`.  Stability alone supplies no equation.  In the other
direction, any construction on `leavitt-steinberg-hs-unstable` refutes the
whole Leavitt lane at once, through
`kl-leavitt-holds-on-the-unstable-steinberg-branch`.
