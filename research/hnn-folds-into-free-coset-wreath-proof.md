---
rg: 2
id: hnn-folds-into-free-coset-wreath-proof
kind: route
title: Push the stable letter through the coset lamps and read reduced forms
target: hnn-folds-into-free-coset-wreath
requires: [gkp-free-wreath-permanence]
artifacts:
  - research/artifacts/hnn-fold-free-coset-wreath-2026-09-11.md
---

`rho(c)` fixes the base coset, so `z_o` commutes with `rho(C)` and the HNN
relation holds in the image. Moving the lamps left writes the image of a
reduced form as `z_(x_1)^(e_1) ... z_(x_k)^(e_k) rho(g)`.

A cancellation `x_(i+1) = x_i` would force the inner syllable into `rho(C')`
(between `t` and `t^(-1)`) or into `rho(C)` (between `t^(-1)` and `t`). Britton
reducedness plus injectivity of `rho` on those syllables forbids this, so
nontrivial elements have nontrivial images. The prerequisite makes the free
coset wreath product sofic when `H` and its coset action are. A group that maps
injectively on every finite subset into sofic groups is sofic. Details in the
artifact.
