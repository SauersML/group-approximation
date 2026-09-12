---
rg: 2
id: fixed-mf-radical-sigma2-completeness-via-universal-quotient
kind: route
title: Give one universal MF quotient a FIN-complete word problem
target: fixed-mf-radical-membership-is-sigma2-complete
requires:
  - universal-mf-quotient
  - mf-radical-membership-has-a-sigma2-upper-bound
  - mf-safe-finite-presentation-compiler
---

Use the exact-radical/compression machinery to construct a finite presentation
`U` with `Res_MF(U)=N`, where membership in the normal subgroup `N` is
`Sigma^0_2`-hard and the visible quotient `U/N` remains MF.  The recursive FIN
switch identifies the desired stable kernel; the missing step is compressing
that kernel into one finite presentation by operations that preserve the MF
visible branch.

Once the exact identity is proved, the computable FIN words land in `N`
exactly on finite c.e. sets.  The universal quotient theorem turns this into
the word problem of `Q_MF(U)`, and the established uniform upper bound supplies
completeness.

