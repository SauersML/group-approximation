---
rg: 2
id: bs14-active-dilation-proves-relative-stability
kind: route
title: Apply the e-quarter threshold and its joint Gram completion
target: bs14-relative-involution-extension-stability
requires:
  - bs14-residual-polar-data-build-active-dilation
---

The active-dilation claim adds `O(e^(1/2)d)=o(d)` dimensions and changes the
tuple by `O(e^(1/8))`.  Its joint Gram completion makes both cubic equations
exact on the active cells, while passive cells have already been discarded
within the same error.  Both the padding fraction and the generator
displacement tend to zero, which is the qualitative flexible endpoint.
