---
rg: 2
id: relative-kazhdan-correction-closes-word-energy
kind: route
title: Decode the module, correct the bimodule, and apply the relative Kazhdan projection
target: infinite-character-actor-word-energy-interface
requires:
  - finite-presentation-must-expose-whole-module-with-uniform-defect
  - lamp-coupled-relative-bimodule-correction
  - relative-kazhdan-bimodule-upgrades-finite-covariance
---

The first input and uniform abelian HS rounding produce one exact
finite-support spectral representation `rho` of the whole module.  Apply
the lamp-coupled correction for each actor generator.  The established
relative-Kazhdan estimate then bounds

```text
sup_(m in M)||pi(s)rho(m)pi(s)^*-rho(s m)||_2
```

by a dimension-independent modulus of the original finite relator defect.
The whole-module averaging identity `(IWE2)` converts that supremum bound to
the complete fine-character transport energy.  The existing infinite
Schreier gap and exclusion of seed-visible finite character orbits then give
the required interface.

