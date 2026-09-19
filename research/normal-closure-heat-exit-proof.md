---
rg: 2
id: normal-closure-heat-exit-proof
kind: route
title: Telescope a fixed denominator normal-closure word through the lattice heat projection
target: normal-closure-heat-exits-control-arithmetic-leak
requires:
  - arithmetic-leak-has-fd-null-laplacian-witness
---

Perfectness makes the quotient by the normal closure of the lattice both
cyclic and perfect, hence trivial, giving the fixed word `(NHE1)`.  Telescope
that word on a lattice-fixed vector.  Each lattice letter kills the fixed
projection, so only the off-fixed component of the corresponding conjugated
vector remains.  The property-`(T)` heat contraction estimates that component
by its cross first-exit and yields `(NHE2)`.
