---
rg: 2
id: bs14-cubic-spectral-rounding-proof
kind: route
title: Nearest-root functional calculus isolates the relative core incidence
target: bs14-cubic-rounding-leaves-relative-core-basin
requires:
  - iwahori-square-root-presentation-is-bs14-plus-one-involution
  - iwahori-uniform-infinitesimal-rigidity
---

The presentation identity gives `(CSR1)`.  Nearest-cube-root functional
calculus gives `(CSR2)` with constant `1/2`, independently of dimension and
multiplicity, and telescoping gives `(CSR3)`.

The corrected pair `Ahat,Bhat` is an exact representation of the free pair
of order-three generators.  Recovering an Iwahori tuple additionally
requires the same corrected `X` and an exact BS core to realize their
relative product.  This is the relative basin statement displayed in the
target, not another consequence of spectral rounding.  Uniform
infinitesimal rigidity explains why the remaining issue is global: within
an existing coordinate tube the derivative is already uniformly
transverse after genuine tangent modes are removed.
