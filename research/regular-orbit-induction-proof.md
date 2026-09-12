---
rg: 2
id: regular-orbit-induction-proof
kind: route
title: Index directional copies by H so left translation makes the product map equivariant
target: regular-orbit-induction-coherifies-finite-edges
requires: []
---

At the factor indexed by `h`, define `Phi_reg` to be
`phi_(h^(-1).x_0)`.  Left translation by `g` sends that factor to `gh`, where
the required directional map is
`phi_((gh)^(-1).g.x_0)=phi_(h^(-1).x_0)`.  This proves `(ROI3)` factor by
factor.  Products of injective maps are injective, and identifying the same
central involution in every factor preserves injectivity on the resulting
central product.  The semidirect extension `(ROI4)` follows.

Tensoring the chosen finite-dimensional factor representations multiplies
both sides of every restriction equation by the same fixed dimensions.
Normalized masses and mismatch ratios are therefore unchanged.  The
completeness and finite exactification assertions use only finite orbit
covariantization and the already available countable amplification.
