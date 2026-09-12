---
rg: 2
id: atlas-q14-full-coefficient-cyclicity-proof
kind: route
title: Put two matrix-algebra generators in the marked transvection centralizer
target: atlas-q14-exact-allows-full-coefficient-cyclicity
requires:
  - atlas-morita-coefficient-cyclicity-reduction
---

The two matrix units `E_13,E_14` commute with the marked nilpotent `E_23`
and have pairwise zero products, so the unipotent chart change `(QFC2)` is
self-inverse and fixes the marked transvection.  Its coefficient algebra
contains the shift `X` and wrap matrix `Y`.  The products `(QFC3)` are all
matrix units, hence the coefficient algebra is full.  Apply the exact Morita
orbit formula to conclude one-dimensional cyclicity.
