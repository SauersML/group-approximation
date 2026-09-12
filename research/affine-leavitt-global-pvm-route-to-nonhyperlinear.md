---
rg: 2
id: affine-leavitt-global-pvm-route-to-nonhyperlinear
kind: route
title: Round the active root module globally and collapse its nontrivial mark by character expansion
target: non-hyperlinear-group
requires:
  - affine-leavitt-global-active-module-exposure
  - all-abelian-uniform-hs-rounding-gives-global-pvm
  - affine-leavitt-global-root-pvm-collapses-active-mark
---

Uniform all-pairs exposure gives a quasirepresentation of the elementary
abelian active root module.  Uniform abelian HS stability rounds it in the
same matrix dimension to one finite-support character PVM.  The actor energy
survives the rounding, and `(AGC2)` makes `x_16(A)` converge to the identity.
But this is a nonidentity root word in the finitely presented group
`St_6(R)`, so canonical-trace hyperlinear microstates would make its distance
from the identity converge to `sqrt(2)`.  Contradiction.

