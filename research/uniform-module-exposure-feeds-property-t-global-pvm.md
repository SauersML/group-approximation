---
rg: 2
id: uniform-module-exposure-feeds-property-t-global-pvm
kind: route
title: Round the exposed whole module by uniform abelian HS stability
target: property-t-must-upgrade-global-augmentation-rounding
requires:
  - finite-presentation-must-expose-whole-module-with-uniform-defect
  - all-abelian-uniform-hs-rounding-gives-global-pvm
---

Apply uniform abelian HS stability to the whole-module map in `(FME1)`.
The result is an exact elementary-abelian representation in the original
matrix dimension and hence one finite-support global spectral PVM.  Uniform
closeness preserves the fixed lamp and transfers the actor covariance with
only twice the rounding error.  Property `(T)` is then used on the actor
orbit energy, not to perform simultaneous diagonalization.

