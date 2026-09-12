---
rg: 2
id: deligne-triple-cover-fd-central-invisibility-proof
kind: route
title: Deligne finite residual plus Malcev kills the triple-cover center in exact matrices
target: deligne-triple-cover-fd-central-invisibility
requires: []
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
---

Deligne's theorem, in the modern formulation recorded for example in Stover,
arXiv:2407.07680, Theorem 1.5, says that for `g>=2` and `n>=3` the inverse
image `Gamma_n` of `Sp_(2g)(Z)` in the connected `n`-fold cover is a central
`Z/n` extension and that the image of `2Z` lies in the intersection of the
kernels of all maps to finite groups.  At `g=2,n=3`, multiplication by two is
an automorphism of `Z/3`.  Hence **every finite quotient of `E_3` kills `z`**.

Now let `rho:E_3->U(d)` be finite-dimensional.  The group `E_3` is finitely
generated (it is a finite central extension of the arithmetic lattice
`Sp_4(Z)`), so `rho(E_3)` is a finitely generated subgroup of `GL_d(C)`.
Malcev's theorem makes `rho(E_3)` residually finite.  If `rho(z)!=1`, some
finite quotient of `rho(E_3)` separates `rho(z)`; composing with `rho` gives a
finite quotient of `E_3` nontrivial on `z`, contradicting Deligne.  Therefore
`rho(z)=1`.
