---
rg: 2
id: full-sl3-tracial-hnn-leak-proof
kind: route
title: Evaluate the regular trace of the centralizer HNN stable letter
target: full-sl3-root-package-has-an-exact-tracial-hnn-leak
requires: []
---

The defining HNN relations put the regular unitary `U=lambda_H(t)` in the
commutant of `rho(Lambda)`.  Restriction of a canonical group trace to a
subgroup is canonical, proving the first line of `(FTH2)`.

For `h notin Lambda`, the word

```text
t h t^(-1) h^(-1)
```

has no HNN pinch: the only candidate base letter adjacent to the stable
letters is `h`, which is outside the associated subgroup `Lambda`.
Britton's lemma makes the word nontrivial.  Its regular trace is zero, while
the lattice commutator words are literally the identity.  All other listed
relations belong to the embedded base group `Gamma` and therefore hold
exactly.  This proves every assertion.
